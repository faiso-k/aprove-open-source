package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;

/**
 * Encodes that newAnnotation was created from oldAnnotation and thus, the
 * length of the connection encoded by newAnnotation is related to the one of
 * oldAnnotation.
 * @author Marc Brockschmidt
 */
public class DefiniteReachabilityAnnotationCreation implements AnnotationInformation {
    private final DefiniteReachabilityAnnotation oldAnnotation;
    private final DefiniteReachabilityAnnotation newAnnotation;
    private final IntegerRelationType relation;

    /**
     * @param oldA the old annotation
     * @param newA the new annotation
     * @param relationParam the relation R describes new R old, where "<" means that the path described by the new
     * annotation is shorter than the path described by the old annotation.
     */
    public DefiniteReachabilityAnnotationCreation(final DefiniteReachabilityAnnotation oldA,
            final DefiniteReachabilityAnnotation newA, final IntegerRelationType relationParam) {
        this.oldAnnotation = oldA;
        this.newAnnotation = newA;
        this.relation = relationParam;
    }

    /**
     * @return the oldAnnotation
     */
    public DefiniteReachabilityAnnotation getOldAnnotation() {
        return this.oldAnnotation;
    }

    /**
     * @return the newAnnotation
     */
    public DefiniteReachabilityAnnotation getNewAnnotation() {
        return this.newAnnotation;
    }

    /**
     * @return the relation with newAnnotation REL oldAnnotation
     */
    public IntegerRelationType getRelation() {
        return this.relation;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.newAnnotation.toString() + " " + this.relation + " " + this.oldAnnotation.toString();
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Define Reachability Inferred");
        res.put("Old annotation", this.oldAnnotation.toSExpString());
        res.put("New annotation", this.newAnnotation.toSExpString());
        res.put("Length elation", this.getRelation().toString());
        return res;
    }
}
