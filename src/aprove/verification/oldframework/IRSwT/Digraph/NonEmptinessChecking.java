package aprove.verification.oldframework.IRSwT.Digraph;

import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Checks whether or not a given rule can be applied.
 * In general this is undecidable, because non-linear arithmetic
 * might occur.
 *
 * @author Matthias Hoelzel
 *
 */
public class NonEmptinessChecking {
    /** Input rule to be checked. */
    private final IGeneralizedRule inputRule;

    /** Formula factory! */
    private final FormulaFactory<SMTLIBTheoryAtom> factory;

    /** Name generator! */
    private final FreshNameGenerator fng;

    /** Some aborter! */
    private final Abortion aborter;

    /**
     * Some rule that should be checked for usability.
     * @param rule some rule
     * @param fac some formula factory
     * @param gen some name generator
     * @param abortion some aborter
     */
    public NonEmptinessChecking(
        final IGeneralizedRule rule,
        final FormulaFactory<SMTLIBTheoryAtom> fac,
        final FreshNameGenerator gen,
        final Abortion abortion)
    {
        this.inputRule = rule;
        this.factory = fac;
        this.fng = gen;
        this.aborter = abortion;
    }

    /**
     * Tries to find out whether or not the given input rule is usable.
     * @return YES, NO or MAYBE. NO means empty.
     * @throws AbortionException can be aborted
     */
    public YNM checkNonEmptiness() throws AbortionException {
        final Formula<SMTLIBTheoryAtom> condition =
            ToolBox.boolTermToSMT_QF_IA(this.inputRule.getCondTerm(), this.factory, this.fng);
        final SMTEngine engine = new SMTLIBEngine();

        try {
            final Abortion subAbortion = this.aborter.createChild(1500);
            final Pair<YNM, Map<String, String>> smtResult =
                engine.solve(Collections.singletonList(condition), SMTLogic.QF_NIA, subAbortion);
            return smtResult.x;
        } catch (final WrongLogicException wle) {
            if (Globals.DEBUG_MATTHIAS) {
                System.err.println(wle);
                wle.printStackTrace();
            }
            // we do not care
            return YNM.MAYBE;
        }
    }
}
