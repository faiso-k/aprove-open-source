package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;

public class SampleConjectureToEqSystemsByIdentity extends SampleConjecturesToEqSystems {

    public SampleConjectureToEqSystemsByIdentity(Collection<RewriteSequence> sampleConjectures,
            GroupingCriterion groupingCriterion,
            SingleSampleConjectureToEqSystem transformer,
            LowerBoundsToolbox toolbox) {
        super(sampleConjectures, groupingCriterion, transformer, toolbox);
    }

    @Override
    SampleConjectureMap newGroup(RewriteSequence conjecture, LowerBoundsToolbox toolbox) {
        return IdentitySampleConjectureMap.fromConjecture(conjecture, toolbox);
    }

}
