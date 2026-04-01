package aprove.verification.oldframework.IntTRS.Nonterm;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Prove non-periodic non-termination. Do it the smart way.
 *
 * @author Marc Brockschmidt
 */
public class IntTRSNonPeriodicNontermProcessor extends IntTRSNontermProcessor {

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (obl instanceof IRSwTProblem) {
            IRSwTProblem problem = ((IRSwTProblem) obl);
            return problem.isIRS() && problem.getStartTerm() == null && Options.certifier.isNone();
        } else {
            return false;
        }
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSProblem problem;
        if (obl instanceof IRSProblem) {
            problem = (IRSProblem) obl;
        } else {
            problem = new IRSProblem((IRSwTProblem) obl);
        }

        final Set<IGeneralizedRule> normalizedRules = IntTRSNontermProcessor.moveFsIntoArgsAndNormalize(problem.getRules());
        final FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<>();

        final List<Formula<SMTLIBTheoryAtom>> firstRunConditionsAndComputation = new LinkedList<>();
        final List<Formula<SMTLIBTheoryAtom>> secondRunNegatedConditions = new LinkedList<>();

        for (final IGeneralizedRule normalizedRule : normalizedRules) {
            final Pair<Formula<SMTLIBTheoryAtom>, Formula<SMTLIBTheoryAtom>> firstRunP =
                IntTRSNontermProcessor.turnRuleIntoSMTFormulae(normalizedRule, "run1_", "run2_", factory);
            firstRunConditionsAndComputation.add(factory.buildAnd(firstRunP.x, firstRunP.y));

            final Pair<Formula<SMTLIBTheoryAtom>, Formula<SMTLIBTheoryAtom>> secondRunP =
                IntTRSNontermProcessor.turnRuleIntoSMTFormulae(normalizedRule, "run2_", "run3_", factory);
            secondRunNegatedConditions.add(factory.buildNot(secondRunP.y));
        }

        final Formula<SMTLIBTheoryAtom> firstRunFormula = factory.buildOr(firstRunConditionsAndComputation);
        final Formula<SMTLIBTheoryAtom> nontermFormula =
            factory.buildAnd(firstRunFormula, factory.buildAnd(secondRunNegatedConditions));

        final SMTEngine smtEngine = new SMTLIBEngine();
        Pair<YNM, Map<String, String>> res;
        try {
            final Abortion subAbortion = aborter.createChild(1000);
            res = smtEngine.solve(Collections.singletonList(nontermFormula), SMTLogic.QF_NIA, subAbortion);
        } catch (final WrongLogicException | AbortionException e) {
            // we do not care
            res = new Pair<>(YNM.MAYBE, null);
        }
        //If the formula is UNSAT, we have a winner. Otherwise, go away:
        if (res.x != YNM.NO) {
            return ResultFactory.unsuccessful();
        }

        //Prove that we can traverse the loop at all:
        try {
            final Abortion subAbortion = aborter.createChild(1000);
            res = smtEngine.solve(Collections.singletonList(firstRunFormula), SMTLogic.QF_NIA, subAbortion);
        } catch (final WrongLogicException | AbortionException e) {
            // we do not care
            res = new Pair<>(YNM.MAYBE, null);
        }
        //If the formula is SAT, we are happy and prove. Otherwise, go away:
        if (res.x != YNM.YES) {
            return ResultFactory.unsuccessful();
        }

        return ResultFactory.disproved(new IntTRSNonPeriodicNontermProof(
            normalizedRules,
            nontermFormula,
            firstRunFormula));
    }

    /**
     * The proof of nontermination.
     * @author Marc Brockschmidt
     */
    private class IntTRSNonPeriodicNontermProof extends DefaultProof {
        /** The set of normalized rules generated. */
        private final Set<IGeneralizedRule> normalizedRules;

        /** The formula that was used to prove non-termination. */
        private final Formula<SMTLIBTheoryAtom> nontermFormula;

        /** The formula that was used to prove the loop usable. */
        private final Formula<SMTLIBTheoryAtom> usableFormula;

        /**
         * @param rules The set of normalized rules generated.
         * @param nontermForm The formula that was used to prove non-termination.
         * @param useForm The formula that was used to prove the loop usable.
         */
        public IntTRSNonPeriodicNontermProof(
            final Set<IGeneralizedRule> rules,
            final Formula<SMTLIBTheoryAtom> nontermForm,
            final Formula<SMTLIBTheoryAtom> useForm)
        {
            this.normalizedRules = rules;
            this.nontermFormula = nontermForm;
            this.usableFormula = useForm;
        }

        /**
         * @return the proof as a nice string representation.
         * @param o an export util helping with formatting.
         * @param level not used.
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();

            res.append("Normalized system to the following form:").append(o.linebreak());
            for (final IGeneralizedRule r : this.normalizedRules) {
                res.append(r.export(o)).append(o.linebreak());
            }

            res
                .append(
                    "Proved unsatisfiability of the following formula, indicating that the system is never left after entering:")
                .append(o.linebreak());
            res.append(this.nontermFormula).append(o.linebreak());

            res
                .append(
                    "Proved satisfiability of the following formula, indicating that the system is entered at least once:")
                .append(o.linebreak());
            res.append(this.usableFormula).append(o.linebreak());

            return res.toString();
        }
    }
}
