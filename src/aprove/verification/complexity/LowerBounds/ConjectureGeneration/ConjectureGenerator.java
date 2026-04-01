package aprove.verification.complexity.LowerBounds.ConjectureGeneration;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;


public class ConjectureGenerator {

    private NarrowingTree tree;
    private ConjectureGenerationHeuristic abortionCriterion;

    public ConjectureGenerator(ConjectureGenerationHeuristic abortionCriterion, NarrowingTree tree) {
        this.abortionCriterion = abortionCriterion;
        this.tree = tree;
    }

    public Conjecture generate() throws AbortionException {
        this.abortionCriterion.reset();
        if (this.abortionCriterion.apply(this.tree)) {
            return this.abortionCriterion.getResult();
        } else {
            return null;
        }
    }

}
