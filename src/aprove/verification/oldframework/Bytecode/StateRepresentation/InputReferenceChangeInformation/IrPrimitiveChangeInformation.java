package aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation;

import java.util.function.BiFunction;
import java.util.function.Function;

import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

public class IrPrimitiveChangeInformation extends IrChangeInformation {

    /* TODO
     * The handling of primitives is very simple at the moment.
     * Commented out is the old approach that used the merge aprove uses for primitives anyway.
     * This however is incorrect in the following case:
     * Currently, when there are 2 seperate write that cause side effects, they will be merged.
     * So merge may represent cases where only one of the 2 representation is valid, and the aprove merge results in a valid over approximation
     * However if both represent modifications, i.e. two ++ instructions, then a merge is not enough.
     * If we store the modification (i.e. +1) instead of the resulting value, better handling of primitive side effects can be possible.
     */


    private AbstractNumber newValue;

    public static IrPrimitiveChangeInformation UNKNOWN_INT = new IrPrimitiveChangeInformation(AbstractInt.getUnknown(IntegerType.UNBOUND));
    public static IrPrimitiveChangeInformation UNKNOWN_FLOAT = new IrPrimitiveChangeInformation(AbstractFloat.create());

    IrPrimitiveChangeInformation(AbstractNumber newValue) {
        this.newValue = newValue;
    }

    public AbstractNumber getNewValue() {
        return newValue;
    }

    @Override
    public boolean containsChange(IrChangeInformation other, BiFunction<AbstractVariableReference, AbstractVariableReference, Boolean> varComparator) {
        if (!(other instanceof IrPrimitiveChangeInformation)) {
            assert false;
            return false;
        }
        IrPrimitiveChangeInformation otherCh = (IrPrimitiveChangeInformation) other;
        if (this.newValue instanceof AbstractInt && otherCh.newValue instanceof AbstractInt) {
            AbstractInt thisInt = (AbstractInt) this.newValue;
            return thisInt.equals(AbstractInt.getUnknown(IntegerType.UNBOUND));

            /* TODO this was the old merge, see if we can use it in some situations
            AbstractInt otherInt = (AbstractInt) otherCh.newValue;
            return thisInt.getLower().compareTo(otherInt.getLower()) <= 0
                    && thisInt.getUpper().compareTo(otherInt.getUpper()) >= 0;
            */
        } else if (this.newValue instanceof AbstractFloat && otherCh.newValue instanceof AbstractFloat) {
            AbstractFloat thisFloat = (AbstractFloat) this.newValue;
            return thisFloat.isUnknown();

            /* TODO this was the old merge, see if we can use it in some situations
            AbstractFloat otherFloat = (AbstractFloat) otherCh.newValue;
            if (thisFloat.isUnknown()) {
                return true;
            } else if (thisFloat.isLiteral() && otherFloat.isLiteral()
                    && thisFloat.getLiteral() == otherFloat.getLiteral()) {
                return true;
            } else {
                return false;
            }
            */
        } else {
            return false;
        }
    }

    @Override
    public ChangeType getChangeType() {
        if (newValue instanceof AbstractInt) {
            return ChangeType.INTEGER;
        } else if (newValue instanceof AbstractFloat) {
            return ChangeType.FLOAT;
        } else {
            assert false;
            return null;
        }
    }

    @Override
    public IrChangeInformation replaceReference(Function<AbstractVariableReference, AbstractVariableReference> replacer) {
        return this;
    }

    @Override
    public IrChangeInformation asChangeFromLowerFrame() {
        return this;
    }

    @Override
    public IrPrimitiveChangeInformation merge(IrChangeInformation other, VariableCache varCache) {
        if (this.containsChange(other, null)) {
            return this;
        }
        if (!(other instanceof IrPrimitiveChangeInformation)) {
            assert false;
            return null;
        }
        //IrPrimitiveChangeInformation otherCh = (IrPrimitiveChangeInformation) other;
        if (this.newValue instanceof AbstractInt) {
            return UNKNOWN_INT;
            /* old merge
            AbstractNumber res = ((AbstractInt) this.newValue).merge(otherCh.newValue, true, IntegerType.UNBOUND)
                    .getMergedVariable();
            return new IrPrimitiveChangeInformation(res);
            */
        } else if (this.newValue instanceof AbstractFloat) {
            return UNKNOWN_FLOAT;
            /* old merge
            AbstractNumber res = ((AbstractFloat) this.newValue).merge(otherCh.newValue).getMergedVariable();
            return new IrPrimitiveChangeInformation(res);
            */
        } else {
            return null;
        }
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((newValue == null) ? 0 : newValue.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        IrPrimitiveChangeInformation other = (IrPrimitiveChangeInformation) obj;
        if (newValue == null) {
            if (other.newValue != null)
                return false;
        } else if (!newValue.equals(other.newValue))
            return false;
        return true;
    }

    @Override
    public String toString() {
        return newValue.toString();
    }

}
