package aprove.input.Programs.llvm.problems;

import aprove.prooftree.Export.Utility.*;
import immutables.*;

/**
 * Input types we can (in principle) analyze.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMQueryInputType implements Immutable, Exportable {

    /**
     * The keyword for an allocation type.
     */
    public static final String ALLOCATION = "Alloc";

    /**
     * The keyword for a String type.
     */
    public static final String STRING = "String";

    /**
     * @param size Minimal allocated size.
     * @param sizeIsIndex Is the allocated size an index of another argument or a constant number of bytes?
     * @return An allocated area type of the specified minimal size.
     */
    public static LLVMQueryInputType createAllocationType(int size, boolean sizeIsIndex) {
        return new LLVMQueryInputType(null, size, null, null, false, sizeIsIndex, null);
    }

    /**
     * @param elementType The type of the array's elements.
     * @return A query input type for an array of unknown size.
     */
    public static LLVMQueryInputType createArrayType(LLVMQueryInputType elementType) {
        return new LLVMQueryInputType(null, -1, null, null, false, false, elementType);
    }

    /**
     * @param elementType The type of the array's elements.
     * @param size Minimal array size.
     * @param sizeIsIndex Is the array size an index of another argument or a constant number of bytes?
     * @return A query input type for an array of known size.
     */
    public static LLVMQueryInputType createArrayType(LLVMQueryInputType elementType, int size, boolean sizeIsIndex) {
        return new LLVMQueryInputType(null, size, null, null, false, sizeIsIndex, elementType);
    }

    /**
     * @param a The annotation specifying the integer type.
     * @return A query input type for an integer.
     */
    public static LLVMQueryInputType createIntType(LLVMIntAnnotation a) {
        // TODO the bit-width is not used yet, but it might be an additional information for the starting query as soon
        // as we handle bounded integer arithmetic
        return new LLVMQueryInputType(a, -1, null, null, false, false, null);
    }

    /**
     * @param name Name of allocated area.
     * @return A query input type for a named allocated area.
     */
    public static LLVMQueryInputType createNamedAllocationType(String name) {
        return new LLVMQueryInputType(null, -1, null, name, false, false, null);
    }

    /**
     * @return A query input type for a String.
     */
    public static LLVMQueryInputType createStringType() {
        return new LLVMQueryInputType(null, -1, null, null, true, false, null);
    }

    /**
     * @param additionalSpace The size of the allocated area after the terminating 0 (inclusive).
     * @param sizeIsIndex Flag indicating whether the space argument is a reference to another argument (true) or a
     *                    constant size (false).
     * @return A query input type for a String with additional space after the terminating 0.
     */
    public static LLVMQueryInputType createStringType(int additionalSpace, boolean sizeIsIndex) {
        return new LLVMQueryInputType(null, additionalSpace, null, null, true, sizeIsIndex, null);
    }

    /**
     * Additional information about the allocated area.
     */
    private final ImmutablePair<Integer, Integer> allocatedBetween;

    /**
     * Annotation for Int types.
     */
    private final LLVMIntAnnotation annotation;

    /**
     * Type of elements if this is an array (null if this is no array).
     */
    private final LLVMQueryInputType arrayContentType;

    /**
     * Is this a zero-terminated String?
     */
    private final boolean isString;

    /**
     * Name of allocated area.
     */
    private final String namedArea;

    /**
     * Additional information about size.
     */
    private final int size;

    /**
     * Is the size an index of another argument or a constant number of bytes?
     */
    private final boolean sizeIsArgumentIndex;

    /**
     * Creates a QueryInputType with the specified integer annotation, size information, allocated interval and name
     * information, String information, and information on whether the size information refers to an index or is a
     * constant.
     * @param a The annotation for Int types.
     * @param s Additional size information.
     * @param interval Additional information about the allocated area.
     * @param name Name of allocated area.
     * @param string Is this a zero-terminated String?
     * @param sizeIsIndex Is the size an index of another argument or a constant number of bytes?
     * @param elementType The element type of an array.
     */
    private LLVMQueryInputType(
        LLVMIntAnnotation a,
        int s,
        ImmutablePair<Integer, Integer> interval,
        String name,
        boolean string,
        boolean sizeIsIndex,
        LLVMQueryInputType elementType
    ) {
        this.annotation = a;
        this.size = s;
        this.allocatedBetween = interval;
        this.namedArea = name;
        this.isString = string;
        this.sizeIsArgumentIndex = sizeIsIndex;
        this.arrayContentType = elementType;
    }

    /* (non-Javadoc)
     * @see aprove.prooftree.Export.Utility.Exportable#export(aprove.prooftree.Export.Utility.Export_Util)
     */
    @Override
    public String export(Export_Util o) {
        if (this.isIntegerType()) {
            // integer type
            return this.getAnnotation().export(o);
        } else if (this.isStringType()) {
            if (this.hasMinimalSize()) {
                if (this.isSizeAnArgumentIndex()) {
                    return LLVMQueryInputType.STRING + "(#" + this.getMinimalSize() + ")";
                } else {
                    return LLVMQueryInputType.STRING + "(" + this.getMinimalSize() + ")";
                }
            } else {
                return LLVMQueryInputType.STRING;
            }
        } else if (this.isNamedAllocation()) {
            return LLVMQueryInputType.ALLOCATION + "(" + this.getNamedArea() + ")";
        } else if (this.isArrayType()) {
            if (this.hasMinimalSize()) {
                if (this.isSizeAnArgumentIndex()) {
                    return this.getArrayContentType().export(o) + "[#" + this.getMinimalSize() + "]";
                } else {
                    return this.getArrayContentType().export(o) + "[" + this.getMinimalSize() + "]";
                }
            } else {
                return this.getArrayContentType().export(o) + "[]";
            }
        } else if (this.hasMinimalSize()) {
            if (this.isSizeAnArgumentIndex()) {
                return LLVMQueryInputType.ALLOCATION + "(#" + this.getMinimalSize() + ")";
            } else {
                return LLVMQueryInputType.ALLOCATION + "(" + this.getMinimalSize() + ")";
            }
        } else {
            return LLVMQueryInputType.ALLOCATION;
        }
    }

    /**
     * @return Additional information about the allocated area.
     */
    public ImmutablePair<Integer, Integer> getAllocatedBetween() {
        return this.allocatedBetween;
    }

    /**
     * @return The annotation for integer types.
     */
    public LLVMIntAnnotation getAnnotation() {
        return this.annotation;
    }

    /**
     * @return The element type of an array.
     */
    public LLVMQueryInputType getArrayContentType() {
        return this.arrayContentType;
    }

    /**
     * @return Additional information about minimal size.
     */
    public int getMinimalSize() {
        return this.size;
    }

    /**
     * @return Name of allocated area (maybe null).
     */
    public String getNamedArea() {
        return this.namedArea;
    }

    /**
     * @return True if this query input type contains information about a (possibly additional) allocation size.
     */
    public boolean hasMinimalSize() {
        return this.size >= 0;
    }

    /**
     * @return True if this query input type represents an array type.
     */
    public boolean isArrayType() {
        return this.arrayContentType != null;
    }

    /**
     * @return True if this query input type represents an integer type.
     */
    public boolean isIntegerType() {
        return this.getAnnotation() != null;
    }

    /**
     * @return True if this query input type represents a named allocation.
     */
    public boolean isNamedAllocation() {
        return this.namedArea != null;
    }

    /**
     * @return Is the size an index of another argument or a constant number of bytes?
     */
    public boolean isSizeAnArgumentIndex() {
        return this.sizeIsArgumentIndex;
    }

    /**
     * @return True if this query input type represents a 0-terminated String type.
     */
    public boolean isStringType() {
        return this.isString;
    }

}
