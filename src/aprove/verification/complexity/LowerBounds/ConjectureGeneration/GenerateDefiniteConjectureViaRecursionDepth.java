package aprove.verification.complexity.LowerBounds.ConjectureGeneration;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem.*;

public class GenerateDefiniteConjectureViaRecursionDepth extends DefiniteConjectureGenerationHeuristic {

    public GenerateDefiniteConjectureViaRecursionDepth(LowerBoundsToolbox toolbox) {
        super(toolbox);
    }

    @Override
    SampleConjecturesToEqSystems getTransformer() {
        return new SampleConjectureToEqSystemsByRecursionDepth(this.sampleConjectures, this.groupingCriterion, this.sampleConjectureTransformer, this.toolbox);
    }

    @Override
    int requiredSamplingPoints() {
        return 3;
    }

}
