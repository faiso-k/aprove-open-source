package aprove.verification.oldframework.IntTRS.PoloRedPair;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.IntTRSPolynomialOrderProcessor.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Eats intTRS problems.
 * @author Matthias Hoelzel
 */
public class IntTRSPolynomialOrderWorker {
    /** Current intTRS problem */
    private final IRSProblem intTRS;

    /** The proof under construction */
    private final IntTRSPoloRedPairProof proof;

    /** Set of intTRS rules (the input) */
    private Set<IGeneralizedRule> rules;

    /** List of simplified rules systems */
    private LinkedList<IRSProblem> resultSystems;

    /** Aborter */
    private final Abortion aborter;

    /** Formula factory */
    private final FormulaFactory<SMTLIBTheoryAtom> factory;

    /** Stores whether or not we have changed the problem. */
    private boolean changedProblem;

    /** Arguments that are passed to this processor. */
    private final PolynomialOrderArguments arguments;

    /** Name generator. */
    private final FreshNameGenerator ng;

    /**
     * Constructor
     * @param intTRSProblem current problem
     * @param abortion an aborter
     * @param proof an awesome proof to be built
     * @param args the current arguments
     */
    public IntTRSPolynomialOrderWorker(
        final IRSProblem intTRSProblem,
        final Abortion abortion,
        final IntTRSPoloRedPairProof proof,
        final PolynomialOrderArguments args)
    {
        this.intTRS = intTRSProblem;
        this.aborter = abortion;
        this.ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        this.factory = new FullSharingFactory<SMTLIBTheoryAtom>();
        this.rules = this.intTRS.getRules();
        this.proof = proof;
        this.arguments = args;
    }

    /**
     * Try to deduce termination.
     * @return a (simplified) intTRS
     * @throws AbortionException can be aborted
     */
    public LinkedList<IRSProblem> work() throws AbortionException {
        this.dumpKittel();

        final RulePreparation rulePreparer = new RulePreparation(this.ng);
        this.rules = rulePreparer.prepare(this.rules);

        this.analyzeRules();

        if (Globals.DEBUG_MATTHIAS) {
            DebugLogger.finishLog("poly");
        }

        return this.resultSystems;
    }

    /**
     * Returns true iff it simplified the problem.
     * @return boolean
     */
    public boolean hasChangedProblem() {
        return this.changedProblem;
    }

    /**
     * Find an order and simplify the given problem
     * @throws AbortionException can be aborted
     */
    private void analyzeRules() throws AbortionException {
        final RuleAnalyzer analyzer =
            new RuleAnalyzer(this.arguments, this.rules, this.factory, this.ng, this.aborter, this.proof);
        final LinkedList<Set<IGeneralizedRule>> results = analyzer.analyze();

        this.resultSystems = new LinkedList<>();
        this.changedProblem = true;
        for (final Set<IGeneralizedRule> resultSystem : results) {
            this.resultSystems.add(new IRSProblem(ImmutableCreator.create(resultSystem)));
            if (resultSystem.size() == this.rules.size()) {
                this.changedProblem = false;
            }
        }
    }

    /**
     * Only used for debugging purposes.
     */
    private void dumpKittel() {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("poly");
            l.logln("The KITTeL we have to wear:\n" + this.intTRS.toString() + "\n");
            l.logln("Here are current arguments: ");
            l.logln("Degree = " + this.arguments.degree);
            l.logln("HuntBinomials = " + this.arguments.factorBinomials);
            l.logln("BoundBehavior = " + this.arguments.boundBehavior);
        }
    }
}
