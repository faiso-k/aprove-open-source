package aprove.input.Programs.llvm.internalStructures.literals;

import java.math.BigInteger;
import java.util.Collections;
import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;


/**
 * @author Janine Repke, CryingShadow
 */
public abstract class LLVMLiteral implements LLVMLiteralExpression, SimpleExpression, LLVMIRExport {

    /**
     * The type of this literal (optional - maybe null for undef or null values).
     * TODO check whether the void type would be more suitable than null
     */
    private final LLVMType type;

    /**
     * @param litType The type of this literal.
     */
    public LLVMLiteral(LLVMType litType) {
        this.type = litType;
    }

    @Override
    public LLVMLiteral applySubstitution(Substitution sigma) {
        return this;
    }

    /**
     * Needed to get the size of an array. This method returns a value if the
     * literal is an integer or a global variable of integer type.
     * @param basicModule An LLVM module containing global variable definitions.
     * @return The bit-width of this literal if it is of integer type.
     * @throws LLVMParseException If the literal cannot be converted to a length.
     */
    public long convertToLength(LLVMModule basicModule) throws LLVMParseException {
        throw new LLVMWrongLengthValueException(this.type);
    }

    @Override
    public BigInteger evaluate() {
        return null;
    }

    @Override
    public BigInteger evaluate(Map<LLVMLiteral, BigInteger> varToVal) {
        return null;
    }

    @Override
    public String getName() {
        return this.getClass().getSimpleName();
    }

    /**
     * @return The type of this literal.
     */
    public LLVMType getType() {
        return this.type;
    }

    @Override
    public Set<LLVMVariableLiteral> getVariables() {
        return Collections.emptySet();
    }

    @Override
    public LLVMLiteralOperation negate() {
        return LLVMLiteralOperation.create(ArithmeticOperationType.MUL, new LLVMRegularIntLiteral(32, -1, false), this);
    }

    @Override
    public LLVMLiteralExpression substitute(Map<LLVMLiteral, ? extends LLVMLiteral> replacement) {
        return replacement.containsKey(this) ? replacement.get(this) : this;
    }

    /**
     * @return A String representation of the internal structure for debugging purposes.
     * TODO remove this stuff?
     */
    public abstract String toDebugString();

    /**
     * Must be overridden in integer literals.
     * @return The int value of this literal if it is an integer literal.
     * @throws UnsupportedOperationException If this is no integer literal.
     */
    public int toInt() throws UnsupportedOperationException {
        throw new UnsupportedOperationException("This literal is no integer!");
    }

    @Override
    public Object toJSON() {
        return this.getName();
    }

    @Override
    public String toLLVMIR() {
        return this.getName();
    }

    @Override
    public String toSExpressionString() {
        return this.getName();
    }

    @Override
    public SMTExpression<SInt> toSMTExp() {
        throw new UnsupportedOperationException("Not yet implemented!");
    }

    @Override
    public LLVMHeuristicTerm transformToLLVMHeuristicTerm(
        Map<LLVMVariableLiteral, LLVMHeuristicVariable> varToRef,
        LLVMHeuristicTermFactory factory
    ) {
        return null;
    }

}
