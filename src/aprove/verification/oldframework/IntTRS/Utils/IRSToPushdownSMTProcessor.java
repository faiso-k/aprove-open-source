package aprove.verification.oldframework.IntTRS.Utils;

import java.util.*;

import aprove.input.Programs.pushdownSMT.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Transform IRS into a pushdown system of integer-using clauses, as used by HSF.
 *
 * @author Marc Brockschmidt
 */
public class IRSToPushdownSMTProcessor extends Processor.ProcessorSkeleton {

    private static String VAR_NAME = "arg";

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
    }

    public static TRSFunctionApplication getEqTerm(TRSTerm a, TRSTerm b) {
        return TRSTerm.createFunctionApplication(
                                                 IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq,
                                                                                     DomainFactory.INTEGER_INTEGER),
                                                 a,
                                                 b);
    }

    private static IGeneralizedRule makeLinear(IGeneralizedRule rule) {
        assert (!rule.getRight().isVariable());
        TRSFunctionApplication lhs = rule.getLeft();
        ImmutableList<TRSTerm> lhsArgs = lhs.getArguments();
        List<TRSTerm> newLHSArgs = new ArrayList<>(lhsArgs.size());
        TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
        ImmutableList<TRSTerm> rhsArgs = rhs.getArguments();
        List<TRSTerm> newRHSArgs = new ArrayList<>(rhsArgs.size());
        TRSSubstitution nameNormalizationSubst = TRSSubstitution.EMPTY_SUBSTITUTION;
        Set<TRSFunctionApplication> eqConds = new LinkedHashSet<>();
        int i = 1;
        for (TRSTerm a : rule.getLeft().getArguments()) {
            TRSVariable v = (TRSVariable) a;
            TRSVariable newV = TRSTerm.createVariable(IRSToPushdownSMTProcessor.VAR_NAME + (i++));
            newLHSArgs.add(newV);
            nameNormalizationSubst = nameNormalizationSubst.compose(TRSSubstitution.create(v, newV));
            eqConds.add(IRSToPushdownSMTProcessor.getEqTerm(v, newV));
        }
        i = 1;
        for (TRSTerm a : ((TRSFunctionApplication) rule.getRight()).getArguments()) {
            TRSVariable newV = TRSTerm.createVariable(IRSToPushdownSMTProcessor.VAR_NAME + (i++) + "P");
            newRHSArgs.add(newV);
            eqConds.add(IRSToPushdownSMTProcessor.getEqTerm(a, newV));
            if (a.isVariable()) {
                TRSVariable v = (TRSVariable) a;
                nameNormalizationSubst = nameNormalizationSubst.compose(TRSSubstitution.create(v, newV));
            }
        }
        final TRSTerm cond = rule.getCondTerm();

        final TRSTerm renamedCond;
        if (cond != null) {
            renamedCond = cond.applySubstitution(nameNormalizationSubst);
        } else {
            renamedCond = cond;
        }

        TRSTerm newCond = renamedCond;
        for (TRSFunctionApplication eq : eqConds) {
            TRSFunctionApplication renamedEq = eq.applySubstitution(nameNormalizationSubst);
            if (renamedEq.getArgument(0).equals(renamedEq.getArgument(1))) {
                //Skip, is v = v
            } else {
                newCond = IDPv2ToIDPv1Utilities.getConjunction(newCond, renamedEq);
            }
        }

        IGeneralizedRule newRule =
                                 IGeneralizedRule.create(
                                                         TRSTerm.createFunctionApplication(lhs.getRootSymbol(),
                                                                                           newLHSArgs),
                                                         TRSTerm.createFunctionApplication(rhs.getRootSymbol(),
                                                                                           newRHSArgs),
                                                         newCond);

        return newRule;
    }

    private static SMTExpression<SInt> intTermToSExp(TRSTerm t) {
        if (t instanceof TRSVariable) {
            return Ints.intVar(((TRSVariable) t).getName());
        } else {
            TRSFunctionApplication f = (TRSFunctionApplication) t;
            FunctionSymbol s = f.getRootSymbol();
            switch (s.getArity()) {
                case 0:
                    return Ints.constant(Long.valueOf(s.getName()));
                case 1:
                    if (s.getName().equals("-")) {
                        return Ints.negate(IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(0)));
                    } else {
                        throw new NotYetImplementedException("No translation for symbol " + f
                                                             + "/1 to SMTLIB S-Expressions implemented yet.");
                    }
                case 2:
                    switch (f.getName()) {
                        case "+":
                            return Ints.add(IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(0)),
                                            IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(1)));
                        case "*":
                            return Ints.times(IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(0)),
                                              IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(1)));
                        case "-":
                            return Ints.subtract(IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(0)),
                                                 IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(1)));
                        default:
                            throw new NotYetImplementedException("No translation for symbol " + f
                                                                 + " to SMTLIB S-Expressions implemented yet.");
                    }
                default:
                    throw new NotYetImplementedException("No translation for symbol " + f
                                                         + " to SMTLIB S-Expressions implemented yet.");
            }
        }
    }

    private static SMTExpression<SBool> boolTermToSExp(TRSTerm t) {
        if (t instanceof TRSVariable) {
            return Core.boolVar(((TRSVariable) t).getName());
        } else {
            TRSFunctionApplication f = (TRSFunctionApplication) t;
            FunctionSymbol s = f.getRootSymbol();
            switch (s.getArity()) {
                case 0:
                    if ("TRUE".equals(s.getName())) {
                        return Core.True;
                    } else if ("FALSE".equals(s.getName())) {
                        return Core.False;
                    } else {
                        throw new NotYetImplementedException("No translation for symbol " + f
                                                             + " to SMTLIB S-Expressions implemented yet.");
                    }
                case 1:
                    if ("!".equals(s.getName())) {
                        return Core.not(IRSToPushdownSMTProcessor.boolTermToSExp(f.getArgument(0)));
                    } else {
                        throw new NotYetImplementedException("No translation for symbol " + f
                                                             + " to SMTLIB S-Expressions implemented yet.");
                    }
                case 2:
                    switch (s.getName()) {
                        case "&&":
                            return Core.and(IRSToPushdownSMTProcessor.boolTermToSExp(f.getArgument(0)),
                                            IRSToPushdownSMTProcessor.boolTermToSExp(f.getArgument(1)));
                        case "||":
                            return Core.or(IRSToPushdownSMTProcessor.boolTermToSExp(f.getArgument(0)),
                                           IRSToPushdownSMTProcessor.boolTermToSExp(f.getArgument(1)));
                        case "<":
                            return Ints.less(IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(0)),
                                             IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(1)));
                        case "<=":
                            return Ints.lessEqual(IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(0)),
                                                  IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(1)));
                        case "!=":
                            return Core.not(Core.equivalent(IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(0)),
                                                            IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(1))));
                        case "=":
                            return Core.equivalent(IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(0)),
                                                   IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(1)));
                        case ">=":
                            return Ints.greaterEqual(IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(0)),
                                                     IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(1)));
                        case ">":
                            return Ints.greater(IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(0)),
                                                IRSToPushdownSMTProcessor.intTermToSExp(f.getArgument(1)));
                        default:
                            throw new NotYetImplementedException("No translation for symbol " + f
                                                                 + " to SMTLIB S-Expressions implemented yet.");
                    }
                default:
                    throw new NotYetImplementedException("No translation for symbol " + f
                                                         + " to SMTLIB S-Expressions implemented yet.");
            }
        }
    }

    @Override
    public Result process(
                          final BasicObligation obl,
                          final BasicObligationNode oblNode,
                          final Abortion aborter,
                          final RuntimeInformation rti) throws AbortionException {
        assert (obl instanceof IRSwTProblem);
        final IRSProblem problem;
        if (obl instanceof IRSProblem) {
            problem = (IRSProblem) obl;
        } else {
            problem = new IRSProblem((IRSwTProblem) obl);
        }

        final Triple<Map<FunctionSymbol, FunctionSymbol>, Map<FunctionSymbol, Integer>, Set<IGeneralizedRule>> normRes =
                                                                                                                       T2ExportTool.normalizeFs(problem.getRules());
        Set<IGeneralizedRule> normalizedArityRules = normRes.getZ();

        int arity = normalizedArityRules.iterator().next().getRootSymbol().getArity();

        //Set up variables:
        LinkedList<NamedSymbol0<?>> preVars = new LinkedList<>();
        LinkedList<NamedSymbol0<?>> postVars = new LinkedList<>();
        for (int i = 1; i <= arity; i++) {
            preVars.addLast(Ints.intVar(IRSToPushdownSMTProcessor.VAR_NAME + i));
            postVars.addLast(Ints.intVar(IRSToPushdownSMTProcessor.VAR_NAME + i + "P"));
        }

        Collection<Triple<String, SMTExpression<SBool>, String>> transitions = new LinkedList<>();
        Collection<String> usedLocations = new LinkedHashSet<>();
        for (IGeneralizedRule rule : normalizedArityRules) {
            IGeneralizedRule linearRule = IRSToPushdownSMTProcessor.makeLinear(rule);
            TRSFunctionApplication lhs = linearRule.getLeft();
            TRSFunctionApplication rhs = (TRSFunctionApplication) linearRule.getRight();
            usedLocations.add(lhs.getName()); //we can ignore it if it has no outgoing trans

            SMTExpression<SBool> constraint;
            if (linearRule.getCondTerm() != null) {
                TRSTerm condTerm = linearRule.getCondTerm();
                Set<TRSVariable> exVars = condTerm.getVariables();
                exVars.removeAll(linearRule.getLeft().getVariables());
                exVars.removeAll(linearRule.getRight().getVariables());

                if (exVars.isEmpty()) {
                    constraint = IRSToPushdownSMTProcessor.boolTermToSExp(condTerm);
                } else {
                    List<Symbol0<? extends Sort>> sortedExVars = new LinkedList<>();
                    for (TRSVariable v : exVars) {
                        sortedExVars.add(Ints.intVar(v.getName())); //optimistically assume that all variables are int...
                    }
                    constraint = Core.<SBool> exists(SBool.representative,
                                                     sortedExVars,
                                                     IRSToPushdownSMTProcessor.boolTermToSExp(condTerm));
                }
            } else {
                constraint = Core.True;
            }

            transitions.add(
                            new Triple<String, SMTExpression<SBool>, String>(
                                                                             lhs.getRootSymbol().getName(),
                                                                             constraint,
                                                                             rhs.getRootSymbol().getName()));
        }

        //Create fresh init location, add transitions to everything:
        String initLoc = "__init";
        assert (!usedLocations.contains(initLoc)) : "Fresh init location was already used after all...";

        TRSFunctionApplication irsStartTerm = problem.getStartTerm();
        if (irsStartTerm != null) {
            transitions.add(
                            new Triple<String, SMTExpression<SBool>, String>(
                                                                             initLoc,
                                                                             Core.True,
                                                                             irsStartTerm.getRootSymbol().getName()));
        } else {
            for (String usedLoc : usedLocations) {
                transitions.add(
                                new Triple<String, SMTExpression<SBool>, String>(
                                                                                 initLoc,
                                                                                 Core.True,
                                                                                 usedLoc));
            }
        }

        final SMTPushdownAutomaton res =
                                       new SMTPushdownAutomaton(
                                                                new PushdownInitInformation("main",
                                                                                            initLoc,
                                                                                            preVars,
                                                                                            Core.True),
                                                                Collections.singletonList(new PushdownProcedureInformation("main",
                                                                                                                           preVars,
                                                                                                                           postVars,
                                                                                                                           transitions)),
                                                                Collections.<PushdownCallInformation> emptyList(),
                                                                Collections.<PushdownReturnInformation> emptyList());

        // previous version: Why should it only be complete if it does not have a start term?
        // YNMImplication implication = problem.getStartTerm() != null ? YNMImplication.SOUND : YNMImplication.EQUIVALENT;

        return ResultFactory.provedAnd(Collections.singletonList(res),
                                       YNMImplication.EQUIVALENT,
                                       new IRSToPushdownProof());

    }

    /**
     * The finest proof.
     * @author Marc Brockschmidt
     */
    public class IRSToPushdownProof extends DefaultProof {

        /** Create the proof. */
        public IRSToPushdownProof() {
            this.shortName = "IRS2Pushdown";
            this.longName = "IRS to SMTLIB Pushdown System Processor";
        }

        /**
         * @param eu export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder builder = new StringBuilder();
            builder.append("Transformed input IRS into a pusshdown system.");
            return builder.toString();
        }
    }
}
