package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;
import java.util.*;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.AbstractBoundedInt.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Parent of all elements occurring in "operations", i.e., arithmetic expressions.
 * @author Janine Repke, cryingshadow
 */
public interface LLVMHeuristicTerm extends LLVMTerm {

    @Override
    default LLVMHeuristicTerm applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this.applySubstitution(Substitution.toSubstitution(sigma));
    }

    @Override
    LLVMHeuristicTerm applySubstitution(Substitution sigma);

    /**
     * @return A set of all sub-expressions of this expression (including this expression).
     */
    Set<LLVMHeuristicTerm> computeAllSubExpressions();

    /**
     * @return The highest absolute multiplicative constant factor occurring in this expression.
     */
    BigInteger computeHighestAbsoluteFactor();

    /**
     * @param valueMap The values for the references.
     * @param params Strategy parameters.
     * @return The evaluation of the expression denoted by this OpNode if it only contains (abstract) integers. Null
     *         otherwise.
     * @throws OverflowException If an overflow occurs.
     */
    AbstractBoundedInt evaluate(Map<LLVMHeuristicVariable, LLVMValue> valueMap, LLVMParameters params)
    throws OverflowException;

    /**
     * @return A list of the additive literals in this expression (no expansion of a product is performed).
     */
    List<LLVMHeuristicTerm> getLiterals();

    /**
     * @return The number of positions within this expression holding a variable.
     */
    int getNumberOfVarOccs();

    @Override
    default LLVMHeuristicTermFactory getTermFactory() {
        return LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY;
    }

    /**
     * @return All symbolic variables (including constant references) occurring in this term.
     */
    @Override
    default Set<? extends LLVMHeuristicVariable> getVariables() {
        return this.getVariables(true);
    }

    /**
     * @param includeConstants Flag indicating whether or not constant references should be included.
     * @return All symbolic variables occurring in this term.
     */
    Set<? extends LLVMHeuristicVariable> getVariables(boolean includeConstants);

    /**
     * @return True if this is a linear expression. False otherwise.
     */
    boolean isLinear();

    /**
     * @return True iff this expression is of the form -x for a variable x.
     */
    boolean isNegatedVariable();

    /**
     * @param values A value function.
     * @return True iff this expression is known to be negative by the value function.
     */
    boolean isNegative(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values);

    /**
     * @param values A value function.
     * @return True iff this expression is known to be non-negative by the value function.
     */
    boolean isNonNegative(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values);

    /**
     * @param values A value function.
     * @return True iff this expression is known to be non-positive by the value function.
     */
    boolean isNonPositive(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values);

    /**
     * @param values A value function.
     * @return True iff this expression is known to be positive by the value function.
     */
    boolean isPositive(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values);

    /**
     * @return True iff this expression is a sum of terms. False otherwise.
     */
    boolean isSum();

    /**
     * @return True iff this expression is of the form x + y for two different variables x and y. False otherwise.
     */
    boolean isSumOfTwoDifferentVariables();

    /**
     * @return True iff this expression is of the form x + c for a variable x and a constant c. False otherwise.
     */
    boolean isSumOfVariableAndConstant();

    @Override
    LLVMHeuristicTerm negate();

    /**
     * @param substitutionMap A mapping from old variable names to new values.
     * @return A copy of this where all occurrences of variables occurring as a key value in the given map are replaced
     *         by the corresponding value in the map.
     */
    LLVMHeuristicTerm substitute(Map<LLVMHeuristicVariable, ? extends LLVMHeuristicTerm> substitutionMap);

    /**
     * @return This expression separated in the part without additive and multiplicative constants and these two
     *         constants (first additive, second multiplicative). So the result (x,a,b) represents the term b * x + a.
     */
    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> toLinear();

}
