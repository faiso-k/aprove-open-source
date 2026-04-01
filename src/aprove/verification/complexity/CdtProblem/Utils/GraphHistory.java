package aprove.verification.complexity.CdtProblem.Utils;

import java.util.*;

import aprove.verification.complexity.CdtProblem.*;

/**
 * Transformation history for a node A.
 */
public class GraphHistory {
    /**
     * This is the tuple B present in the original dependency graph, from
     * which A was created via transformations.
     */
    private final Cdt origTuple;

    /**
     * For each element in this set, a node A (or one of the nodes A descended
     * from) was at least once narrowed by the transformation processor
     * associated with this elemen.
     *
     * XXX: Maybe extend this to a map to integers, to allow a better
     * parameterization?
     */
    private final EnumMap<Technique, Integer> transformations;

    public GraphHistory(Cdt origTuple,
            EnumMap<Technique,Integer> transformations) {
        this.origTuple = origTuple;
        this.transformations = transformations;
    }

    public static GraphHistory createEmpty(Cdt tuple) {
        return new GraphHistory(tuple, new EnumMap<Technique, Integer>(Technique.class));
    }

    public GraphHistory createTransformed(Technique technique) {
        EnumMap<Technique,Integer> newTrans =
            new EnumMap<Technique, Integer>(this.transformations);
        if (technique != null) {
            Integer cnt = newTrans.get(technique);
            if (cnt == null) {
                newTrans.put(technique, 0);
            } else {
                newTrans.put(technique, cnt.intValue() + 1);
            }
        }
        return new GraphHistory(this.getOrigTuple(), newTrans);
    }


    public Cdt getOrigTuple() {
        return this.origTuple;
    }


    public int getTransformations(Technique technique) {
        Integer cnt = this.transformations.get(technique);
        return (cnt == null ? 0 : cnt.intValue());
    }


    public static enum Technique {
        Narrowing, Instantiation, ForwardInstantiation, Rewriting
    }

}