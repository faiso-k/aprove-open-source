package aprove.verification.complexity.CdtProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Utility.*;

public class ComplexCdtProblemProcessor extends ProcessorSkeleton {

    private static final Proof IsEmptyProof = new IsEmptyProof();

    @Override
    public Result process(
        BasicObligation obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
    ) throws AbortionException {
        ComplexCdtProblem problem = (ComplexCdtProblem)obl;
        if (problem.isEmpty()) {
            return ResultFactory.provedWithValue(
                ComplexityYNM.create(
                    ComplexityValue.constant(),
                    ComplexityValue.constant()
                ),
                ComplexCdtProblemProcessor.IsEmptyProof
            );
        }
        if (problem.multiply()) {
            return ResultFactory.provedMult(
                problem.getTodos(),
                BothBounds.create(),
                new MultiplicationProof()
            );
        } else {
            return ResultFactory.provedMax(
                problem.getTodos(),
                BothBounds.create(),
                new MaxProof()
            );
        }
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof ComplexCdtProblem;
    }

    private static class IsEmptyProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("The set of problems is empty.");
        }

    }

    public class MultiplicationProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME real proof?
            return "Multiplied the complexity of the problems.";
        }

    }

    public class MaxProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME real proof?
            return "Took the maximum complexity of the problems.";
        }

    }

}
