package aprove.verification.complexity.LowerBounds.ConjectureGeneration;

import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;


public abstract class DefiniteConjectureGenerationHeuristic extends ConjectureGenerationHeuristic {

    public DefiniteConjectureGenerationHeuristic(LowerBoundsToolbox toolbox) {
        super(toolbox, new DefiniteGroupingCriterion(toolbox));
    }

    @Override
    @SuppressWarnings("incomplete-switch")
    public Conjecture getResult() {
        if (this.model == null) {
            return null;
        }
        TRSFunctionApplication lhs = this.getStartTerm().applySubstitution(refinement);
        TRSTerm rhs = this.samplingPoints.getScheme();
        for (RulePosition pos: this.model.positions()) {
            TRSTerm replacement = this.toolbox.pfHelper.normalize(this.model.toTerm(pos, this.toolbox));
            switch (pos.side) {
                case LEFT:
                    lhs = (TRSFunctionApplication) lhs.replaceAt(pos.pos, replacement);
                    break;
                case RIGHT:
                    rhs = rhs.replaceAt(pos.pos, replacement);
                    break;
            }
        }
        return new Conjecture(lhs, rhs);
    }

    @Override
    boolean isRelevant(RewriteSequence sc) {
        return true;
    }

    @Override
    SingleSampleConjectureToEqSystem getSampleConjectureTransformer() {
        return new BothSidesToEqSystem(this.toolbox);
    }

    @Override
    List<RewriteSequence> getRewriteSequencesToConsider(NarrowingTree tree) {
        return tree.normalForms();
    }
}

