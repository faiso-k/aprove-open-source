package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;

public interface GroupingCriterion {

    boolean fits(SampleConjectureMap map, RewriteSequence conjecture);

}
