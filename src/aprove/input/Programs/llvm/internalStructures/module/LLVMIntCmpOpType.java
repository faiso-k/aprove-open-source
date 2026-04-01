package aprove.input.Programs.llvm.internalStructures.module;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * Operation types for integer compare operations.
 * @author Janine Repke, CryingShadow
 */
public enum LLVMIntCmpOpType {

    /**
     * Equal.
     */
    EQ {

        @Override
        public IntegerRelationType getIntegerRelationType() {
            return IntegerRelationType.EQ;
        }

        @Override
        public boolean signed() {
            return true;
        }

    },

    /**
     * Not equal.
     */
    NE {

        @Override
        public IntegerRelationType getIntegerRelationType() {
            return IntegerRelationType.NE;
        }

        @Override
        public boolean signed() {
            return true;
        }

    },

    /**
     * Signed greater than or equal to.
     */
    SGE {

        @Override
        public IntegerRelationType getIntegerRelationType() {
            return IntegerRelationType.GE;
        }

        @Override
        public boolean signed() {
            return true;
        }

    },

    /**
     * Signed greater than.
     */
    SGT {

        @Override
        public IntegerRelationType getIntegerRelationType() {
            return IntegerRelationType.GT;
        }

        @Override
        public boolean signed() {
            return true;
        }

    },

    /**
     * Signed less than or equal to.
     */
    SLE {

        @Override
        public IntegerRelationType getIntegerRelationType() {
            return IntegerRelationType.LE;
        }

        @Override
        public boolean signed() {
            return true;
        }

    },

    /**
     * Signed less than.
     */
    SLT {

        @Override
        public IntegerRelationType getIntegerRelationType() {
            return IntegerRelationType.LT;
        }

        @Override
        public boolean signed() {
            return true;
        }

    },

    /**
     * Unsigned greater than or equal to.
     */
    UGE {

        @Override
        public IntegerRelationType getIntegerRelationType() {
            return IntegerRelationType.GE;
        }

        @Override
        public boolean signed() {
            return false;
        }

    },

    /**
     * Unsigned greater than.
     */
    UGT {

        @Override
        public IntegerRelationType getIntegerRelationType() {
            return IntegerRelationType.GT;
        }

        @Override
        public boolean signed() {
            return false;
        }

    },

    /**
     * Unsigned less than or equal to.
     */
    ULE {

        @Override
        public IntegerRelationType getIntegerRelationType() {
            return IntegerRelationType.LE;
        }

        @Override
        public boolean signed() {
            return false;
        }

    },

    /**
     * Unsigned less than.
     */
    ULT {

        @Override
        public IntegerRelationType getIntegerRelationType() {
            return IntegerRelationType.LT;
        }

        @Override
        public boolean signed() {
            return false;
        }

    };

    /**
     * @return The corresponding IntegerRelationType.
     */
    public abstract IntegerRelationType getIntegerRelationType();

    /**
     * @return Is this a signed comparison? Also true if the comparison can be used for both signed and unsigned
     *         comparisons.
     */
    public abstract boolean signed();

    @Override
    public String toString() {
        return this.name().toLowerCase();
    }

}
