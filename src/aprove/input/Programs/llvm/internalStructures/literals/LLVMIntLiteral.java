package aprove.input.Programs.llvm.internalStructures.literals;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * Super class for integer literals.
 * @author CryingShadow
 */
public abstract class LLVMIntLiteral extends LLVMLiteral implements IntegerConstant {

    /**
     * @param type The type (must be an integer type).
     */
    protected LLVMIntLiteral(LLVMType type) {
        super(type);
        if (Globals.useAssertions) {
            assert (type.isIntType()) : "Type is no integer type!";
        }
    }

    @Override
    public LLVMIntLiteral applySubstitution(Substitution sigma) {
        return this;
    }

    @Override
    public long convertToLength(LLVMModule module) throws LLVMParseException {
        return this.getValueAsLong();
    }

    @Override
    public BigInteger evaluate() {
        return this.getValueAsBigInteger();
    }

    @Override
    public BigInteger evaluate(Map<LLVMLiteral, BigInteger> varToVal) {
        return this.getValueAsBigInteger();
    }

    /**
     * @return The boolean value of this integer (0 = false, 1 = true).
     * @throws NumberFormatException If the value is neither 0 or 1.
     */
    public boolean getBooleanValue() throws NumberFormatException {
        if (this.getValueAsLong() == 0) {
            return false;
        } else if (this.getValueAsLong() == 1) {
            return true;
        } else {
            throw new NumberFormatException("The value is no boolean value!");
        }
    }

    /**
     * @return The value of this constant.
     */
    public BigInteger getIntegerValue() {
        return this.getValueAsBigInteger();
    }

    /**
     * @return The value as BigInteger.
     */
    public abstract BigInteger getValueAsBigInteger();

    /**
     * @return The value as long.
     * @throws NumberFormatException If the value is not representable as long.
     */
    public abstract long getValueAsLong() throws NumberFormatException;

    @Override
    public Set<LLVMVariableLiteral> getVariables() {
        return Collections.emptySet();
    }

    /**
     * @return True iff the value is 0 or 1.
     */
    public boolean isBooleanValue() {
        return this.getValueAsLong() == 0 || this.getValueAsLong() == 1;
    }

    @Override
    public String toDOTString() {
        return this.getValueAsBigInteger().toString();
    }

    @Override
    public LLVMHeuristicTerm transformToLLVMHeuristicTerm(
        Map<LLVMVariableLiteral, LLVMHeuristicVariable> varToRef,
        LLVMHeuristicTermFactory factory
    ) {
        return factory.constant(this.getValueAsBigInteger());
    }

}
