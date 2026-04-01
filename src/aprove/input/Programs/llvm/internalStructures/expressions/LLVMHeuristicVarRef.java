package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;
import java.util.*;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.AbstractBoundedInt.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Reference to an abstract variable.
 * @author jhensel, cryingshadow
 */
public class LLVMHeuristicVarRef extends LLVMHeuristicVariable {

    /**
     * A place holder for limit variables of allocated memory areas - used in program relations to be inferred.
     */
    public static final LLVMHeuristicVariable endOfAllocatedArea = new LLVMHeuristicVarRef("end");

    /**
     * A place holder for size variables of allocated memory areas - used in program relations to be inferred.
     */
    public static final LLVMHeuristicVariable sizeOfAllocatedArea = new LLVMHeuristicVarRef("size");

    /**
     * A place holder for start variables of allocated memory areas - used in program relations to be inferred.
     */
    public static final LLVMHeuristicVariable startOfAllocatedArea = new LLVMHeuristicVarRef("start");

    /**
     * Create a new reference to an AbstractVariable. Should not be used outside of factory methods (this is why it is
     * package private).
     * @param name the name of this reference.
     */
    LLVMHeuristicVarRef(String name) {
        super(name);
    }

    /**
     * Create a new reference to an AbstractVariable. Should not be used outside of factory methods (this is why it is
     * package private).
     * @param name the name of this reference.
     * @param dName The debug name.
     */
    LLVMHeuristicVarRef(String name, String dName) {
        super(name, dName);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof LLVMHeuristicVariable)) {
            return false;
        }
        LLVMHeuristicVariable other = (LLVMHeuristicVariable)obj;
        if (this.getName() == null) {
            if (other.getName() != null) {
                return false;
            }
        } else if (!this.getName().equals(other.getName())) {
            return false;
        }
        return true;
    }

    @Override
    public AbstractBoundedInt evaluate(Map<LLVMHeuristicVariable, LLVMValue> valueMap, LLVMParameters params)
    throws OverflowException {
        return valueMap.get(this).getThisAsAbstractBoundedInt();
    }

    @Override
    public int getNumberOfVarOccs() {
        return 1;
    }

    @Override
    public Set<? extends LLVMHeuristicVariable> getVariables(boolean includeConstants) {
        return Collections.<LLVMHeuristicVariable>singleton(this);
    }

    @Override
    public boolean isConcrete() {
        return false;
    }

    @Override
    public boolean isNegative(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        LLVMValue val = values.get(this);
        if (val == null) {
            return false;
        }
        // TODO change this as soon as we have other values than integers
        return val.getThisAsAbstractBoundedInt().isNegative();
    }

    @Override
    public boolean isNonNegative(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        LLVMValue val = values.get(this);
        if (val == null) {
            return false;
        }
        // TODO change this as soon as we have other values than integers
        return val.getThisAsAbstractBoundedInt().isNonNegative();
    }

    @Override
    public boolean isNonPositive(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        LLVMValue val = values.get(this);
        if (val == null) {
            return false;
        }
        // TODO change this as soon as we have other values than integers
        return val.getThisAsAbstractBoundedInt().isNonPositive();
    }

    @Override
    public boolean isPositive(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        LLVMValue val = values.get(this);
        if (val == null) {
            return false;
        }
        // TODO change this as soon as we have other values than integers
        return val.getThisAsAbstractBoundedInt().isPositive();
    }

    @Override
    public Triple<LLVMHeuristicTerm, BigInteger, BigInteger> toLinear() {
        return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(this, BigInteger.ZERO, BigInteger.ONE);
    }

//    @Override
//    public SMTLIBIntValue toSMTIntValue() {
//        // TODO: Are also boolean variables possible
//        return SMTLIBIntVariable.create(this.toString());
//    }

}
