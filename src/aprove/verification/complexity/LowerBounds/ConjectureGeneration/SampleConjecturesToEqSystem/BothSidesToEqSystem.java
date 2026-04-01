package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.RulePosition.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class BothSidesToEqSystem extends SingleSampleConjectureToEqSystem {

    public BothSidesToEqSystem(LowerBoundsToolbox toolbox) {
        super(toolbox);
    }

    @Override
    void transformRhs(TRSSubstitution refinement) throws NotTransformableException {
        TRSTerm s =
            this.toolbox.genEqRewriter.normalizeRL(this.sampleConjecture.getResult().applySubstitution(refinement));
        for (Pair<Position, TRSTerm> p : s.getPositionsWithSubTerms()) {
            TRSTerm t = p.y;
            if (PFHelper.isInt(t)) {
                this.addConstraint(Side.RIGHT, p.x, t);
            }
        }
    }

}
