package aprove.input.Programs.llvm.problems;

import aprove.prooftree.Export.Utility.*;
import immutables.*;

/**
 * Additional information about int types.
 * @author cryingshadow
 * @version $Id$
 */
public enum LLVMIntAnnotation implements Immutable, Exportable {

    /**
     * Negative int.
     */
    NEGATIVE("Neg"),

    /**
     * Non-negative int.
     */
    NON_NEGATIVE("NonNeg"),

    /**
     * Non-positive int.
     */
    NON_POSITIVE("NonPos"),

    /**
     * No additional information (arbitrary int).
     */
    NONE("Int"),

    /**
     * Positive int.
     */
    POSITIVE("Pos");

    /**
     * The representation String.
     */
    private final String representation;

    /**
     * @param r The representation String.
     */
    private LLVMIntAnnotation(String r) {
        this.representation = r;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Export.Utility.Exportable#export(aprove.prooftree.Export.Utility.Export_Util)
     */
    @Override
    public String export(Export_Util o) {
        return this.getRepresentation();
    }

    /**
     * @return The representation String.
     */
    public String getRepresentation() {
        return this.representation;
    }

}
