package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.*;


public class LeftSideToEqSystem extends SingleSampleConjectureToEqSystem {

    public LeftSideToEqSystem(LowerBoundsToolbox toolbox) {
        super(toolbox);
    }

    @Override
    void transformRhs(TRSSubstitution refinement) throws NotTransformableException {
        // do nothing
    }

}
