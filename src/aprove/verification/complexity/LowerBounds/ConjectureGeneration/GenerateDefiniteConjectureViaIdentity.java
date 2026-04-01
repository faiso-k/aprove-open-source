package aprove.verification.complexity.LowerBounds.ConjectureGeneration;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem.*;

public class GenerateDefiniteConjectureViaIdentity extends DefiniteConjectureGenerationHeuristic {

    public GenerateDefiniteConjectureViaIdentity(LowerBoundsToolbox toolbox) {
        super(toolbox);
    }

    @Override
    SampleConjecturesToEqSystems getTransformer() {
        return new SampleConjectureToEqSystemsByIdentity(this.sampleConjectures, this.groupingCriterion, this.sampleConjectureTransformer, this.toolbox);
    }

    @Override
    int requiredSamplingPoints() {
        return 3;
    }

}
