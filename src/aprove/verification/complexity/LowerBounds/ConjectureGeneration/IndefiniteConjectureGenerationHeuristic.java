package aprove.verification.complexity.LowerBounds.ConjectureGeneration;

import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;

public class IndefiniteConjectureGenerationHeuristic extends ConjectureGenerationHeuristic {

    public IndefiniteConjectureGenerationHeuristic(LowerBoundsToolbox toolbox) {
        super(toolbox, new IndefiniteGroupingCriterion());
    }

    @Override
    public Conjecture getResult() {
        if (this.model == null) {
            return null;
        }
        TRSFunctionApplication lhs = this.getStartTerm().applySubstitution(refinement);
        for (RulePosition pos : this.model.positions()) {
            TRSTerm replacement = this.toolbox.pfHelper.normalize(this.model.toTerm(pos, this.toolbox));
            switch (pos.side) {
                case LEFT:
                    lhs = (TRSFunctionApplication) lhs.replaceAt(pos.pos, replacement);
                    break;
                default: break;
            }
        }
        return new Conjecture(lhs, this.toolbox.arbitraryTerm);
    }

    @Override
    SingleSampleConjectureToEqSystem getSampleConjectureTransformer() {
        return new LeftSideToEqSystem(this.toolbox);
    }

    @Override
    boolean isRelevant(RewriteSequence sc) {
        return this.sampleConjectures.size() < 20 && !sc.isEmpty() && sc.getLast().getRule().getRootSymbol().equals(sc.getStartTerm().getRootSymbol());
    }

    @Override
    int requiredSamplingPoints() {
        return 3;
    }

    @Override
    SampleConjecturesToEqSystems getTransformer() {
        return new SampleConjectureToEqSystemsByRecursionDepth(this.sampleConjectures, this.groupingCriterion, this.sampleConjectureTransformer, this.toolbox);
    }

    @Override
    List<RewriteSequence> getRewriteSequencesToConsider(NarrowingTree tree) {
        return tree.all();
    }
}
