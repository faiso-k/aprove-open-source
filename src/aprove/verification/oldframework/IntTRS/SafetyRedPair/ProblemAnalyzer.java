package aprove.verification.oldframework.IntTRS.SafetyRedPair;

//import immutables.Immutable.ImmutableCreator;
//
//import java.util.HashSet;
//import java.util.List;
//import java.util.Map;
//import java.util.Set;
//
//import aprove.verification.dpframework.BasicStructures.FunctionApplication;
//import aprove.verification.dpframework.IDPProblem.IGeneralizedRule;
//import aprove.verification.oldframework.Algebra.Polynomials.SimplePolynomial;
//import aprove.verification.oldframework.IntTRS.IRSProblem;
//import aprove.verification.oldframework.IntTRS.IRSwTProblem;
//import aprove.verification.oldframework.IntTRS.SafetyRedPair.SafetyIntTRSPolynomialOrderProcessor.SafetyIntTRSPoloRedPairProof;
//import aprove.verification.oldframework.IntTRS.SafetyRedPair.SafetyIntTRSPolynomialOrderProcessor.SafetyPolynomialOrderArguments;
//import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.*;
//import aprove.verification.oldframework.PropositionalLogic.FormulaFactory;
//import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBTheoryAtom;
//import aprove.verification.oldframework.Utility.FreshNameGenerator;
//import aprove.strategies.Abortions.Abortion;
//import aprove.strategies.Abortions.AbortionException;


/**
 * @author marinag
 * Program termination analyzer
 */
class ProblemAnalyzer {

//    private final IRSwTProblem intTRSProblem;
//
//    private final Abortion aborter;
//
//    private final SafetyPolynomialOrderArguments arguments;
//
//    private final SafetyIntTRSPoloRedPairProof proof;
//
//    private IRSwTProblem resultProblem;
//
//    public ProblemAnalyzer(
//        final SafetyPolynomialOrderArguments args,
//        final IRSwTProblem intTRS,
//        final FormulaFactory<SMTLIBTheoryAtom> formulaFactory,
//        final FreshNameGenerator gen, final Abortion abortion,
//        final SafetyIntTRSPoloRedPairProof intTRSProof
//    ) {
//        this.intTRSProblem = intTRS;
//        this.aborter = abortion;
//        this.arguments = args;
//        this.proof = intTRSProof;
//    }
//
//    /**
//     * @return remaining IRSwTProblem
//     * @throws AbortionException
//     */
//    public IRSwTProblem analyze() throws AbortionException {
//        if (this.intTRSProblem.getStartTerm() == null) {
//            return this.intTRSProblem;
//        }
//        if (this.resultProblem != null) {
//            return this.resultProblem;
//        }
//        final Set<IGeneralizedRule> removedRules = new HashSet<>(); //this.intTRSProblem.getRules());
//        Map<FunctionApplication, List<SimplePolynomial>> ranking;
//        final Cooperation cooperation = Cooperation.create(this.intTRSProblem, this.aborter);
//        this.aborter.checkAbortion();
//        final CooperationResult result = cooperation.getResult(this.arguments.partialSolution);
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
//    }

}
