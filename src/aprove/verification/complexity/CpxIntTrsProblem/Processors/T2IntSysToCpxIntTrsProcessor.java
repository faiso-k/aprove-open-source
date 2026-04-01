package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.util.*;
import java.util.Collections;

import aprove.input.Programs.t2.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IntTRS.Compression.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Converts a T2-style integer transition system to an CpxIntTRS. Useful mostly for converting .t2 problems to .cint problems.
 * @author Marc Brockschmidt, Fabian Emmes
 */
public class T2IntSysToCpxIntTrsProcessor extends Processor.ProcessorSkeleton {
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof T2IntSys;
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        final T2IntSys intSys = (T2IntSys) obl;

        //Get the ssa forms of everything:
        final Map<T2IntTrans, Pair<TRSTerm, Map<TRSVariable, TRSTerm>>> transSemantics = new LinkedHashMap<>();
        for (final T2IntTrans trans : intSys.getTransitions()) {
            transSemantics.put(trans, trans.getGuardAndVarUpdate());
        }

        //Find all variables ever assigned or used (order needs to be stable!):
        final LinkedHashSet<TRSVariable> vars = new LinkedHashSet<>();
        for (final T2IntTrans trans : intSys.getTransitions()) {
            final Pair<TRSTerm, Map<TRSVariable, TRSTerm>> p = transSemantics.get(trans);
            vars.addAll(p.y.keySet());
            if (p.x != null) {
                vars.addAll(p.x.getVariables());
            }
        }

        //Do not encode $random things into the arguments:
        final Iterator<TRSVariable> it = vars.iterator();
        while (it.hasNext()) {
            final TRSVariable v = it.next();
            if (v.getName().startsWith("$nondet")) {
                it.remove();
            }
        }

        Set<IGeneralizedRule> resTRS = new LinkedHashSet<>();
        final ImmutableArrayList<TRSVariable> variableList = ImmutableCreator.create(new ArrayList<>(vars));

        final FunctionSymbol startSymbol = FunctionSymbol.create("f" + intSys.getStartState(), vars.size());

        for (final T2IntTrans trans : intSys.getTransitions()) {
            final TRSFunctionApplication sourceTerm =
                TRSTerm.createFunctionApplication(
                    FunctionSymbol.create("f" + trans.getFromState(), vars.size()),
                    variableList);

            final ArrayList<TRSTerm> rightTerms = new ArrayList<>(vars.size());
            final Pair<TRSTerm, Map<TRSVariable, TRSTerm>> p = transSemantics.get(trans);
            final Map<TRSVariable, TRSTerm> varUpdate = p.y;
            for (final TRSVariable var : vars) {
                final TRSTerm argTerm;
                if (varUpdate.containsKey(var)) {
                    argTerm = varUpdate.get(var);
                } else {
                    argTerm = var;
                }
                rightTerms.add(argTerm);
            }
            final TRSFunctionApplication targetTerm =
                TRSTerm
                    .createFunctionApplication(FunctionSymbol.create("f" + trans.getToState(), vars.size()), rightTerms);

            final TRSTerm guard = p.x;
            resTRS.add(IGeneralizedRule.create(sourceTerm, targetTerm, guard));
        }

        RuleCombiner combiner = new RuleCombiner(resTRS, Collections.emptySet(), aborter);
        resTRS = combiner.combineRules(false, true).y;

        final ArrayList<TRSVariable> startVars = new ArrayList<>(vars.size());
        for (int i = 1; i <= vars.size(); i++) {
            startVars.add(TRSTerm.createVariable("x" + i));
        }

        resTRS =
            TerminationSCCToIDPv1Processor.cleanConstraints(resTRS, false, true, IDPPredefinedMap.DEFAULT_MAP, aborter);
        resTRS = TerminationSCCToIDPv1Processor.removeTrivialConstraints(resTRS, IDPPredefinedMap.DEFAULT_MAP);
        resTRS = TerminationSCCToIDPv1Processor.removePredefinedOpsOnLhs(resTRS, IDPPredefinedMap.DEFAULT_MAP);
        resTRS = IRSwTFormatTransformer.makeLhsLinear(resTRS, IDPPredefinedMap.DEFAULT_MAP);

        final LinkedHashSet<CpxIntTupleRule> res = new LinkedHashSet<>();
        for (final IGeneralizedRule rule : resTRS) {
            try {
                final IGeneralizedRule com_rule =
                    IGeneralizedRule.create(
                        rule.getLeft(),
                        TRSTerm.createFunctionApplication(CpxIntTermHelper.getComSymbol(1), rule.getRight()),
                        rule.getCondTerm());
                // add Com_1 around RHS
                res.addAll(CpxIntTupleRule.createRules(com_rule));
            } catch (final NoValidCpxIntTupleRuleException e) {
                System.err.println("Failed to process " + rule);
                System.err.println(e.getMessage());
                return ResultFactory.error(e);
            }
        }

        final LinkedHashSet<FunctionSymbol> startSymbols = new LinkedHashSet<>();
        startSymbols.add(startSymbol);

        return ResultFactory.proved(
            CpxIntTrsProblem.create(ImmutableCreator.create(res), ImmutableCreator.create(startSymbols)),
            YNMImplication.SOUND,
            new T2IntSysToCpxIntTrsProof());
    }

    /**
     * Well. A boring proof.
     */
    private static class T2IntSysToCpxIntTrsProof extends Proof.DefaultProof {
        /**
         * This creates a boring proof.
         */
        public T2IntSysToCpxIntTrsProof() {
            this.setShortName("T2IntSysToCpxIntTrsProof");
            this.setLongName("T2IntSysToCpxIntTrsProof");
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Transformed T2-style integer transition system to CpxIntTrs.";
        }
    }
}
