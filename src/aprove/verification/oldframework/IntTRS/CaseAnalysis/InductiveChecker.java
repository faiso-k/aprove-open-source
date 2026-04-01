package aprove.verification.oldframework.IntTRS.CaseAnalysis;

import java.util.*;

import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Checks whether or not a given GECondition is inductive for a rewrite system
 * R, i.e., whether for all terms t, s where t satisfies the condition and t
 * ->_R s implies that s also satisfies the given condition.
 * @author Matthias Hoelzel
 */
public class InductiveChecker {
    /** The input condition to be checked. */
    private final GEZeroCondition inputCondition;

    /** Input rewrite system. */
    private final IRSwTProblem inputSystem;

    /** Some formula factory. */
    private final FormulaFactory<SMTLIBTheoryAtom> factory;

    /** Some fresh name generator! */
    private final FreshNameGenerator ng;

    /** Some aborter. Reminds when time is up. */
    private final Abortion aborter;

    /** Stores SMT-Solvers result. */
    private Pair<YNM, Map<String, String>> res;

    /** The result of this class. */
    private Boolean result;

    /**
     * Constructor
     * @param condition input condition
     * @param system input system
     * @param formFactory some formulae factory
     * @param abortion some aborter
     * @param gen some name generator
     */
    public InductiveChecker(
        final GEZeroCondition condition,
        final IRSwTProblem system,
        final FormulaFactory<SMTLIBTheoryAtom> formFactory,
        final Abortion abortion,
        final FreshNameGenerator gen)
    {
        this.inputCondition = condition;
        this.inputSystem = system;
        this.factory = formFactory;
        this.aborter = abortion;
        this.ng = gen;

        assert condition != null && system != null && formFactory != null && abortion != null && gen != null : "I don't like null!";
    }

    /**
     * Uses an SMT-Solver to compute whether or not the given condition is indeed
     * inductive w.r.t. the input system.
     * @return boolean
     * @throws AbortionException can be aborted
     */
    public boolean check() throws AbortionException {
        if (this.result != null) {
            return this.result;
        }

        final LinkedList<Formula<SMTLIBTheoryAtom>> formulae = new LinkedList<>();

        // No rule should break the condition:
        for (final IGeneralizedRule rule : this.inputSystem.getRules()) {
            // Get the interesting parts of the rule
            final TRSFunctionApplication leftFuncy = rule.getLeft();
            final TRSFunctionApplication rightFuncy = (TRSFunctionApplication) rule.getRight();
            TRSTerm ruleCondition = rule.getCondTerm();
            ruleCondition = ruleCondition == null ? ToolBox.buildTrue() : ruleCondition;

            // Translate these parts to SMT constraints
            final Formula<SMTLIBTheoryAtom> leftFuncySatisfiesCond =
                this.inputCondition.buildCorrespondingGEConstraint(leftFuncy, this.ng, this.factory);
            final Formula<SMTLIBTheoryAtom> rightFuncySatisfiesCond =
                this.inputCondition.buildCorrespondingGEConstraint(rightFuncy, this.ng, this.factory);
            final Formula<SMTLIBTheoryAtom> ruleConditionSMT =
                ToolBox.boolTermToSMT_QF_IA(ruleCondition, this.factory, this.ng);

            // Construct constraint, expressing that this rule is mad:
            final Formula<SMTLIBTheoryAtom> ruleIsMadSMT =
                this.factory.buildAnd(
                    this.factory.buildAnd(leftFuncySatisfiesCond, ruleConditionSMT),
                    this.factory.buildNot(rightFuncySatisfiesCond));
            formulae.add(ruleIsMadSMT);
        }

        final Formula<SMTLIBTheoryAtom> toBeUnsat = this.factory.buildOr(formulae);

        // Check whether or not no rule is mad:
        final SMTEngine smtEngine = new SMTLIBEngine();
        try {
            this.res = smtEngine.solve(Collections.singletonList(toBeUnsat), SMTLogic.QF_NIA, this.aborter);
        } catch (final WrongLogicException e) {
            this.res = new Pair<>(YNM.MAYBE, null);
        }

        if (this.res.x != YNM.NO) {
            // There is some bad guy:
            this.result = false;
        } else {
            // Every rule is happy:
            this.result = true;
        }

        return this.result;
    }

    /**
     * Returns the result of the SMT-solver.
     * @return YNM and a model
     */
    public Pair<YNM, Map<String, String>> getSMTResult() {
        return this.res;
    }
}
