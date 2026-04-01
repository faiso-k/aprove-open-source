package aprove.input.Programs.llvm.internalStructures.literals;

import java.math.*;
import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

/**
 * Parent of all elements occurring in "operations", i.e., arithmetic expressions.
 * @author Jera Hensel
 */
public interface LLVMLiteralExpression extends FunctionalIntegerExpression {

    /**
     * Evaluates an expression if there are no variables.
     * @return The evaluated expression as BigInteger.
     */
    BigInteger evaluate();

    /**
     * Evaluates an expression replacing the variables by integers.
     * @param varToVal Mapping of variables to integers.
     * @return The evaluated expression as BigInteger.
     */
    BigInteger evaluate(Map<LLVMLiteral, BigInteger> varToVal);

    @Override
    Set<LLVMVariableLiteral> getVariables();

    /**
     * @param replacement A map from literals to literals.
     * @return This literal expression where each key literal is replaced by the corresponding value literal
     *         simultaneously.
     */
    LLVMLiteralExpression substitute(Map<LLVMLiteral, ? extends LLVMLiteral> replacement);

    /**
     * Transforms a BasicLiteralExpression to an LLVMHeuristicTerm.
     * @param varToRef The mapping of program literals to symbolic variables.
     * @param factory The term factory to build LLVMHeuristicTerms.
     * @return The expression where program variables are substituted by symbolic variables.
     */
    LLVMHeuristicTerm transformToLLVMHeuristicTerm(
        Map<LLVMVariableLiteral, LLVMHeuristicVariable> varToRef,
        LLVMHeuristicTermFactory factory
    );

}
