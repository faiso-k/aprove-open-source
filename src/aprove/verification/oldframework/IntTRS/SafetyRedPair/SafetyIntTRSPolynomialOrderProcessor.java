package aprove.verification.oldframework.IntTRS.SafetyRedPair;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.IntTRS.*;

/**
 * Processor for applying path-based (non-)termination proving methods via interpolation.
 * @author marinag, cryingshadow
 */
public class SafetyIntTRSPolynomialOrderProcessor extends Processor.ProcessorSkeleton {

    /**
     * The strategy arguments for the processor.
     */
    private final SafetyPolynomialOrderArguments arguments;

    /**
     * A class for the strategy arguments.
     */
    public static class SafetyPolynomialOrderArguments {

        /**
         * TODO document me
         */
        public boolean partialSolution = false;

    }

    /**
     * @param args The strategy arguments.
     */
    public SafetyIntTRSPolynomialOrderProcessor(SafetyPolynomialOrderArguments args) {
        this.arguments = args;
    }

    /**
     * Sets default arguments.
     */
    public SafetyIntTRSPolynomialOrderProcessor() {
        this.arguments = new SafetyPolynomialOrderArguments();
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem)obl).getStartTerm() != null;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
    throws AbortionException {
        assert (obl instanceof IRSwTProblem);
        final IRSwTProblem intTRSProblem = (IRSwTProblem) obl;
//        final SafetyIntTRSPoloRedPairProof proof = new SafetyIntTRSPoloRedPairProof();
        final SafetyIntTRSPolynomialOrderWorker worker =
            new SafetyIntTRSPolynomialOrderWorker(intTRSProblem, aborter, this.arguments);
        return worker.work().toResult();
//        if (worker.hasProved()) {
//            return ResultFactory.proved(proof);
//        } else if (worker.hasDisproved()) {
//            return ResultFactory.disproved(proof);
//        } else {
//            return ResultFactory.provedAnd(toSolve, YNMImplication.EQUIVALENT,proof);
//        }
    }

}
