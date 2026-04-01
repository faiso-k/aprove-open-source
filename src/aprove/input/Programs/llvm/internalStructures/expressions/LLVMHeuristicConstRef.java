package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;
import java.util.*;

import org.json.*;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.AbstractBoundedInt.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Represents a standard reference to a constant integer value.
 * @author cryingshadow
 */
public class LLVMHeuristicConstRef extends LLVMHeuristicVariable implements LLVMConstant {

    /**
     * The value represented by this constant reference.
     */
    private final BigInteger value;

    /**
     * Standard constructor. Should not be used outside of factory methods (this is why it is package private).
     * @param number The value to be referenced.
     */
    public LLVMHeuristicConstRef(BigInteger number) {
        super("IConst" + number.toString());
        this.value = number;
    }

    @Override
    public Expression accept(Visitor<Expression, Expression> v) {
        return v.visit(this);
    }

    @Override
    public LLVMHeuristicConstRef applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this;
    }

    @Override
    public LLVMHeuristicConstRef applySubstitution(Substitution sigma) {
        return this;
    }

    /**
     * @return This constant marked to be unmerged.
     */
    public LLVMNonMergedConstRef asUnmerged() {
        return new LLVMNonMergedConstRef(this.value);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof LLVMHeuristicConstRef)) {
            return false;
        }
        LLVMHeuristicConstRef other = (LLVMHeuristicConstRef)obj;
        return this.getIntegerValue().equals(other.getIntegerValue());
    }

    @Override
    public AbstractBoundedInt evaluate(Map<LLVMHeuristicVariable, LLVMValue> valueMap, LLVMParameters params)
    throws OverflowException {
        AbstractBoundedInt resLiteral = AbstractBoundedInt.create(this.value);
        return resLiteral;
    }

    @Override
    public BigInteger getIntegerValue() {
        return this.value;
    }

    @Override
    public int getNumberOfVarOccs() {
        return 0;
    }

    /**
     * @return The value of this constant references as an AbstractInt
     */
    public AbstractBoundedInt getValueAsAbstractBoundedInt() {
        return AbstractBoundedInt.create(this.value);
    }

    @Override
    public Set<? extends LLVMHeuristicVariable> getVariables(boolean includeConstants) {
        return
            includeConstants ?
                Collections.<LLVMHeuristicVariable>singleton(this) :
                    Collections.<LLVMHeuristicVariable>emptySet();
    }

    @Override
    public int hashCode() {
        return this.value.hashCode() * 3;
    }

    @Override
    public boolean isConcrete() {
        return true;
    }

    @Override
    public boolean isNegative(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        return this.value.compareTo(BigInteger.ZERO) < 0;
    }

//    @Override
//    public SMTLIBIntValue toSMTIntValue() {
//        return SMTLIBIntConstant.create(this.getIntegerValue());
//    }

    @Override
    public boolean isNonNegative(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        return this.value.compareTo(BigInteger.ZERO) >= 0;
    }

    @Override
    public boolean isNonPositive(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        return this.value.compareTo(BigInteger.ZERO) <= 0;
    }

    @Override
    public boolean isPositive(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        return this.value.compareTo(BigInteger.ZERO) > 0;
    }

    @Override
    public boolean isZero() {
        return BigInteger.ZERO.compareTo(this.value) == 0;
    }

    @Override
    public LLVMHeuristicConstRef negate() {
        return new LLVMHeuristicConstRef(this.value.negate());
    }

    @Override
    public String toDOTString() {
        return this.toString();
    }

    @Override
    public JSONObject toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", this.getClass().getSimpleName());
        res.put("value", this.getIntegerValue().toString());
        return res;
    }

    @Override
    public Triple<LLVMHeuristicTerm, BigInteger, BigInteger> toLinear() {
        return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(null, this.value, null);
    }

    @Override
    public String toPrettyString() {
        BigInteger val = this.getIntegerValue();
        return val.compareTo(BigInteger.ZERO) < 0 ? "(" + val.toString() + ")" : val.toString();
    }

    @Override
    public String toSExpressionString() {
        return this.getName();
    }

    @Override
    public SMTExpression<SInt> toSMTExp() {
        return Ints.constant(this.getIntegerValue());
    }

    @Override
    public String toString() {
        return this.value.compareTo(BigInteger.ZERO) < 0 ? "(" + this.value.toString() + ")" : this.value.toString();
    }

    @Override
    public TRSTerm toTerm() {
        return TRSTerm.createFunctionApplication(FunctionSymbol.create(this.value.toString(), 0));
    }

}
