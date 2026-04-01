package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Utility.*;

public class DerivationalComplexityIsAtLeastLinearProcessor extends ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        Set<Rule> R;
        boolean srs;
        if (obl instanceof DerivationalComplexityTrsProblem) {
            R = ((DerivationalComplexityTrsProblem) obl).getR();
            srs = ((DerivationalComplexityTrsProblem) obl).getSignature().stream().allMatch(x -> x.getArity() <= 1);
        } else {
            R = ((DerivationalComplexityRelTrsProblem) obl).getR();
            srs = ((DerivationalComplexityRelTrsProblem) obl).getSignature().stream().allMatch(x -> x.getArity() <= 1);
        }
        if (srs) {
            return ResultFactory.unsuccessful();
        } else if (R.isEmpty()) {
            return ResultFactory.provedWithValue(ComplexityYNM.CONSTANT, new RIsEmptyProof());
        } else {
            return ResultFactory.provedWithValue(ComplexityYNM.createLower(ComplexityValue.linear()), new DerivationalComplexityIsAtLeastLinearProof());
        }
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof DerivationalComplexityTrsProblem || obl instanceof DerivationalComplexityRelTrsProblem) && Options.certifier == Certifier.NONE;
    }

    class DerivationalComplexityIsAtLeastLinearProof extends DefaultProof  {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Derivational Complexity is at least linear";
        }

    }

    class RIsEmptyProof extends DefaultProof  {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "R is empty";
        }

    }

}
