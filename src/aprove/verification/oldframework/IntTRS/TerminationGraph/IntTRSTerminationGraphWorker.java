package aprove.verification.oldframework.IntTRS.TerminationGraph;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.TerminationGraph.IntTRSTerminationGraphProcessor.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Builds the graph and splits it up into the SCCs.
 * @author Matthias Hoelzel
 */
public class IntTRSTerminationGraphWorker {
    /** Current intTRS */
    private final IRSProblem intTRSProblem;

    /** The proof under construction */
    private final IntTRSTerminationGraphProof proof;

    /** Set of KITTeL-rules */
    private Set<IGeneralizedRule> rules;

    /** Aborter */
    private final Abortion aborter;

    /** Formula factory */
    private final FormulaFactory<SMTLIBTheoryAtom> factory;

    /** Stores whether or not we have changed the problem. */
    private boolean changedProblem;

    /** Arguments that are passed to the kittel processor. */
    private final TerminationGraphArguments arguments;

    /** Name generator. */
    private final FreshNameGenerator ng;

    /**
     * Constructor
     * @param intTRSP current problem
     * @param abortion an aborter
     * @param proof an awesome proof to be built
     * @param args the current arguments
     */
    public IntTRSTerminationGraphWorker(
        final IRSProblem intTRSP,
        final Abortion abortion,
        final IntTRSTerminationGraphProof proof,
        final TerminationGraphArguments args)
    {
        this.intTRSProblem = intTRSP;
        this.aborter = abortion;
        this.ng = intTRSP.createFreshNameGenerator();
        this.factory = new FullSharingFactory<SMTLIBTheoryAtom>();
        this.rules = this.intTRSProblem.getRules();
        this.proof = proof;
        this.arguments = args;
    }

    /**
     * Try to deduce termination.
     * @return YNM
     * @throws AbortionException can be aborted
     */
    public List<IRSProblem> work() throws AbortionException {
        final RulePreparation rulePreparer = new RulePreparation(this.ng);
        this.rules = rulePreparer.prepare(this.rules);

        final List<IRSProblem> toSolve = this.analyzeTerminationGraph();
        assert toSolve != null;

        if (Globals.DEBUG_MATTHIAS) {
            DebugLogger.finishLog("graph");
        }

        return toSolve;
    }

    /**
     * Returns true iff it simplified the problem.
     * @return boolean
     */
    public boolean hasChangedProblem() {
        return this.changedProblem;
    }

    /**
     * Builds the TerminationGraph and returns its SCCs. This way a given
     * KITTeLProblem can be split up into smaller problems.
     * @return List of KITTeLProblems.
     * @throws AbortionException can be aborted
     */
    private List<IRSProblem> analyzeTerminationGraph() throws AbortionException {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger logger = DebugLogger.getLogger("graph");
            logger.logln("KITTeLRules:");
            for (final IGeneralizedRule iRule : this.rules) {
                logger.logln(iRule.toString());
            }
        }

        // 0. Initialize and check, whether or not something has to be done!
        final List<IRSProblem> result = new LinkedList<IRSProblem>();
        if (this.rules.isEmpty()) {
            // Hey, nothing to do!
            return result;
        }

        // 1. Build graph:
        final TerminationGraph graph =
            TerminationGraph.buildGraph(
                this.rules,
                this.intTRSProblem.getStartTerm(),
                this.factory,
                this.aborter,
                this.ng,
                this.proof);
        this.aborter.checkAbortion();

        // 2. Get SCCs:
        final List<Set<IGeneralizedRule>> sccs;
        if (this.arguments.useChaining) {
            sccs =
                graph.getSimplifiedSCCs(this.arguments.useConstraintTransformation, this.arguments.defaultChainingOnly);
        } else {
            sccs = graph.getNTSCCs();
        }
        for (final Set<IGeneralizedRule> scc : sccs) {
            assert !scc.isEmpty();
            final IRSProblem kp = new IRSProblem(ImmutableCreator.create(scc));
            result.add(kp);
        }

        if (this.proof != null) {
            this.proof.setNumberOfSCCs(result.size());
        }

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger logger = DebugLogger.getLogger("graph");
            logger.logln("SCCs:");
            for (final IRSwTProblem kp : result) {
                logger.logln(kp.toString());
            }
        }
        this.aborter.checkAbortion();

        // 3. Did this change the problem?
        if (sccs.size() == 1) {
            if (!(sccs.get(0).equals(this.rules))) {
                this.changedProblem = true;
            }
        } else {
            this.changedProblem = true;
        }

        return result;
    }
}
