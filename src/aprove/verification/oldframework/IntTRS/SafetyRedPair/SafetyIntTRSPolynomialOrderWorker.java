package aprove.verification.oldframework.IntTRS.SafetyRedPair;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.SafetyIntTRSPolynomialOrderProcessor.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.*;


/**
 * @author marinag
 *
 */
public class SafetyIntTRSPolynomialOrderWorker {

    /**
     * Current intTRS problem.
     */
    private final IRSwTProblem intTRS;

//    /**
//     * The proof under construction.
//     */
//    private final SafetyIntTRSPoloRedPairProof proof;

//    /**
//     * List of simplified rules systems.
//     */
//    private LinkedList<IRSwTProblem> resultSystems;

    /**
     * Aborter.
     */
    private final Abortion aborter;

//    /**
//     * Formula factory.
//     */
//    private final FormulaFactory<SMTLIBTheoryAtom> factory;

//    /**
//     * Stores whether or not we have changed the problem.
//     */
//    private boolean changedProblem;
//
//    private boolean disproved;
//
//    private boolean proved;

    /**
     * Arguments that are passed to this processor.
     */
    private final SafetyPolynomialOrderArguments arguments;

//    /**
//     * Name generator.
//     */
//    private final FreshNameGenerator ng;

    /**
     * Constructor
     * @param intTRSProblem current problem
     * @param abortion an aborter
     * @param proof an awesome proof to be built
     * @param args the current arguments
     */
    public SafetyIntTRSPolynomialOrderWorker(
        final IRSwTProblem intTRSProblem,
        final Abortion abortion,
//        final SafetyIntTRSPoloRedPairProof proof,
        final SafetyPolynomialOrderArguments args
    ) {
        this.intTRS = intTRSProblem;
        this.aborter = abortion;
//        this.ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
//        this.factory = new FullSharingFactory<SMTLIBTheoryAtom>();
//        this.proof = proof;
        this.arguments = args;
    }

    /**
     * Analyze the current problem for (non-)termination.
     * @return The analysis result (may be null if the current problem has no start terms).
     * @throws AbortionException Can be aborted.
     */
    public CooperationResult work() throws AbortionException {
//        this.analyzeRules();
//        return this.resultSystems;
        if (this.intTRS.getStartTerm() == null) {
            return null;
        }
//        final Set<IGeneralizedRule> removedRules = new LinkedHashSet<>(); //this.intTRSProblem.getRules());
//        Map<FunctionApplication, List<SimplePolynomial>> ranking;
        final Cooperation cooperation = Cooperation.create(this.intTRS, this.aborter);
        this.aborter.checkAbortion();
//        final CooperationResult result =
        return cooperation.getResult(this.arguments.partialSolution);
//        if (result.getType().equals(CooperationResult.Type.NONTERMINATING)) {
//            return null;
//        }
//        ranking = result.getRanking();
//        this.proof.setRanking(result.getRanking());
//        if (result.getType().equals(CooperationResult.Type.TERMINATING)) {
//            this.proof.setTerminating();
//            return this.resultProblem = new IRSProblem(ImmutableCreator.create(new HashSet<IGeneralizedRule>()));
//        }
//        this.aborter.checkAbortion();
//        final Set<IGeneralizedRule> rules = new HashSet<>(this.intTRSProblem.getRules());
//        rules.removeAll(removedRules);
//        this.proof.setDroppedRules(result.getDropped());
//        this.resultProblem = result.getRemaining();
//        return this.resultProblem;
    }

//    /**
//     * Returns true iff it simplified the problem.
//     * @return boolean
//     */
//    public boolean hasChangedProblem() {
//        return this.changedProblem;
//    }

//    /**
//     * Find an order and simplify the given problem
//     * @throws AbortionException can be aborted
//     */
//    private void analyzeRules() throws AbortionException {
//        final ProblemAnalyzer analyzer =
//            new ProblemAnalyzer(this.arguments, this.intTRS, this.factory, this.ng, this.aborter, this.proof);
//        this.resultSystems = new LinkedList<>();
//        final IRSwTProblem result = analyzer.analyze();
//        if (result == null) {
//            this.disproved = true;
//        } else {
//            this.proved = result.getRules().isEmpty();
//            this.resultSystems.add(result);
//            this.disproved = false;
//        }
//    }

//    public boolean hasDisproved() {
//        return this.disproved;
//    }
//
//    public boolean hasProved() {
//        return this.proved;
//    }

}
