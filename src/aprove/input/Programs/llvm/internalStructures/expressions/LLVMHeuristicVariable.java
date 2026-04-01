package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;

/**
 * A symbolic variable with heuristics extensions.
 * @author cryingshadow
 * @version $Id$
 */
public abstract class LLVMHeuristicVariable extends LLVMSymbolicVariable implements LLVMHeuristicTerm {

    /**
     * Create a new symbolic variable.
     * @param name The name.
     */
    protected LLVMHeuristicVariable(String name) {
        super(name);
    }

    /**
     * Create a new symbolic variable.
     * @param name The name.
     * @param dName The debug name.
     */
    protected LLVMHeuristicVariable(String name, String dName) {
        super(name, dName);
    }

    @Override
    public LLVMHeuristicTerm applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        if (sigma.containsKey(this)) {
            return (LLVMHeuristicTerm)sigma.get(this);
        }
        return this;
    }

    @Override
    public LLVMHeuristicTerm applySubstitution(Substitution sigma) {
        return (LLVMHeuristicTerm)sigma.substitute(this);
    }

    @Override
    public Set<LLVMHeuristicTerm> computeAllSubExpressions() {
        return Collections.<LLVMHeuristicTerm>singleton(this);
    }

    @Override
    public BigInteger computeHighestAbsoluteFactor() {
        return BigInteger.ONE;
    }

    @Override
    public List<LLVMHeuristicTerm> getLiterals() {
        return Collections.<LLVMHeuristicTerm>singletonList(this);
    }

    @Override
    public Set<? extends LLVMHeuristicVariable> getVariables() {
        return this.getVariables(true);
    }

    /**
     * @return True if this reference points to a concrete value instead of a variable representing several values.
     */
    public abstract boolean isConcrete();

    @Override
    public boolean isLinear() {
        return true;
    }

    @Override
    public boolean isNegatedVariable() {
        return false;
    }

    /**
     * @return True if this reference is known to be the null constant.
     */
    public boolean isZero() {
        // override in constant reference
        return false;
    }

    @Override
    public boolean isSum() {
        return false;
    }

    @Override
    public boolean isSumOfTwoDifferentVariables() {
        return false;
    }

    @Override
    public boolean isSumOfVariableAndConstant() {
        return false;
    }

    @Override
    public LLVMHeuristicTerm negate() {
        return (LLVMHeuristicTerm)LLVMTerm.negate(this, this.getTermFactory());
    }

    @Override
    public LLVMHeuristicTerm substitute(Map<LLVMHeuristicVariable, ? extends LLVMHeuristicTerm> substitution) {
        return substitution.containsKey(this) ? substitution.get(this) : this;
    }

}
