package aprove.verification.oldframework.IntTRS.Utils;

import java.util.*;

import aprove.input.Programs.intClauses.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Transform IRS into a system of integer-using clauses, as used by HSF.
 *
 * @author Marc Brockschmidt
 */
public class IRSToIntClausesProcessor extends Processor.ProcessorSkeleton {
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti
    ) throws AbortionException {
        assert (obl instanceof IRSwTProblem);
        final IRSProblem problem;
        if (obl instanceof IRSProblem) {
            problem = (IRSProblem) obl;
        } else {
            problem = new IRSProblem((IRSwTProblem) obl);
        }
        final Triple<Map<FunctionSymbol, FunctionSymbol>, Map<FunctionSymbol, Integer>, Set<IGeneralizedRule>> normRes =
            T2ExportTool.normalizeFs(problem.getRules());
        final Map<FunctionSymbol, FunctionSymbol> fsToNewFsMap = normRes.x;
        final Map<FunctionSymbol, Integer> fsToPCMap = normRes.y;
        final Set<IGeneralizedRule> normalizedRules =
                IRSwTFormatTransformer.makeLhsLinear(normRes.z, IDPPredefinedMap.DEFAULT_MAP);
        List<TRSTerm> args = null;
        final Set<IntTransitionClause> transitions = new LinkedHashSet<>();
        final FunctionSymbol eq = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Eq, DomainFactory.INTEGER_INTEGER);
        for (IGeneralizedRule rule : normalizedRules) {
            //lhs now has form f(X0, X1, ..., Xn) -> g(t0, ..., tn) [cond] (and is left-linear, as we pushed equalities into the cond)
            rule = rule.getWithRenumberedVariables("X");
            final ImmutableList<TRSTerm> lhsArgs = rule.getLeft().getArguments();
            args = lhsArgs; //this should be the same every time
            final TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
            final ImmutableList<TRSTerm> rhsArgs = rhs.getArguments();
            TRSTerm cond = rule.getCondTerm();
            for (int i = 0; i < lhsArgs.size(); i++) {
                final TRSVariable var = (TRSVariable) lhsArgs.get(i);
                final TRSVariable primedVar = TRSTerm.createVariable(var.getName() + "P");
                final TRSTerm newVal = rhsArgs.get(i);
                cond = IDPv2ToIDPv1Utilities.getConjunction(cond, TRSTerm.createFunctionApplication(eq, primedVar, newVal));
            }

            final Integer sourceLoc = fsToPCMap.get(rule.getLeft().getRootSymbol());
            final Integer targetLoc = fsToPCMap.get(rhs.getRootSymbol());
            transitions.add(new IntTransitionClause(sourceLoc, cond, targetLoc));
        }

        //Yes, I hate you too, you tacked on generic type system that doesn't allow me to cast this shit here:
        final ArrayList<TRSVariable> variables = new ArrayList<>(args.size());
        for (final TRSTerm t : args) {
            variables.add((TRSVariable) t);
        }

        final Integer startLoc;
        if (problem.getStartTerm() != null) {
            startLoc = fsToPCMap.get(fsToNewFsMap.get(problem.getStartTerm().getRootSymbol()));
        } else {
            //Add a start state:
            final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
            for (final Integer id : fsToPCMap.values()) {
                fne.lockName(id.toString());
            }
            startLoc = Integer.valueOf(fne.getFreshName("0", false));

            for (final Integer id : fsToPCMap.values()) {
                TRSTerm cond = null;
                for (final TRSVariable var : variables) {
                    final TRSVariable primedVar = TRSTerm.createVariable(var.getName() + "P");
                    cond = IDPv2ToIDPv1Utilities.getConjunction(cond,
                                                                TRSTerm.createFunctionApplication(eq, primedVar, var));
                }
                transitions.add(new IntTransitionClause(startLoc, cond, id));
            }
        }

        final IntClausesSystem res = new IntClausesSystem(startLoc, variables, transitions);
        return ResultFactory.provedAnd(Collections.singletonList(res),
                                       problem.getStartTerm() != null
                                                                     ? YNMImplication.SOUND : YNMImplication.EQUIVALENT,
                                       new IRSToIntClausesProof(fsToPCMap));

    }

    /**
     * The finest proof.
     * @author Marc Brockschmidt
     */
    public class IRSToIntClausesProof extends DefaultProof {

        /** Map from function symbols to location IDs */
        private final Map<FunctionSymbol, Integer> pcMap;

        /** Create the proof. */
        public IRSToIntClausesProof(final Map<FunctionSymbol, Integer> map) {
            this.shortName = "IRS2Clauses";
            this.longName = "IRS to Integer Clauses Processor";
            this.pcMap = map;
        }

        /**
         * @param eu export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder builder = new StringBuilder();
            builder.append("Transformed input IRS into an system of integer clauses."
                           + "Used the following mapping from defined symbols to location IDs:");
            builder.append(eu.linebreak());

            final List<Pair<String, String>> l = new LinkedList<>();
            for (final Map.Entry<FunctionSymbol, Integer> e : this.pcMap.entrySet()) {
                l.add(new Pair<>(e.getKey().toString(), e.getValue().toString()));
            }
            builder.append(eu.set(l, Export_Util.RULES));
            return builder.toString();
        }
    }
}