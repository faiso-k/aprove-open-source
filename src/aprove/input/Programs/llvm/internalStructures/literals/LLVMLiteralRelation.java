package aprove.input.Programs.llvm.internalStructures.literals;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * A Relation models dependencies between program variables.
 * @author Jera Hensel
 */
public final class LLVMLiteralRelation implements IntegerRelation {

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation left = operand1 + operand2.
     */
    public static LLVMLiteralRelation createAdditionRelation(
        LLVMLiteralExpression left,
        LLVMLiteralExpression operand1,
        LLVMLiteralExpression operand2
    ) {
        return
            new LLVMLiteralRelation(
                IntegerRelationType.EQ,
                left,
                LLVMLiteralOperation.create(ArithmeticOperationType.ADD, operand1, operand2)
            );
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation left = operand1 * operand2.
     */
    public static LLVMLiteralRelation createMultiplicationRelation(
        LLVMLiteralExpression left,
        LLVMLiteralExpression operand1,
        LLVMLiteralExpression operand2
    ) {
        return
            new LLVMLiteralRelation(
                IntegerRelationType.EQ,
                left,
                LLVMLiteralOperation.create(ArithmeticOperationType.MUL, operand1, operand2)
            );
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation left = operand1 - operand2.
     */
    public static LLVMLiteralRelation createSubtractionRelation(
        LLVMLiteralExpression left,
        LLVMLiteralExpression operand1,
        LLVMLiteralExpression operand2
    ) {
        return
            new LLVMLiteralRelation(
                IntegerRelationType.EQ,
                left,
                LLVMLiteralOperation.create(ArithmeticOperationType.SUB, operand1, operand2)
            );
    }

    /**
     * The left-hand side of the relation.
     */
    private final LLVMLiteralExpression lhs;

    /**
     * The right-hand side of the relation.
     */
    private final LLVMLiteralExpression rhs;

    /**
     * The type of the relation (corresponds to relational operator).
     */
    private final IntegerRelationType type;

    /**
     * @param relType The type of the relation.
     * @param left The left-hand side of the relation.
     * @param right The right-hand side of the relation.
     */
    public LLVMLiteralRelation(
        IntegerRelationType relType,
        LLVMLiteralExpression left,
        LLVMLiteralExpression right
    ) {
        if (Globals.useAssertions) {
            assert (relType != null) : "Relation without type detected!";
            assert (left != null) : "Relation without left-hand side detected!";
            assert (right != null) : "Relation without right-hand side detected!";
        }
        this.type = relType;
        this.lhs = left;
        this.rhs = right;
    }

    /**
     * Checks if a simple LT or LE relation with interval values holds in a state for the in the relation contained
     * program variables, using only the states' values but not its relations.
     * @param state The state to check.
     * @return True iff this relation holds in the specified state.
     */
    public boolean checkIntervalRelation(LLVMHeuristicState state) {
        if (!this.isSimple()) {
            return false;
        }
        switch (this.getRelationType()) {
            case EQ:
            case NE:
                return false;
            default:
        }
        Map<LLVMLiteral, BigInteger> varToVal = new LinkedHashMap<LLVMLiteral, BigInteger>();
        if (this.getLhs() instanceof LLVMVariableLiteral) {
            LLVMVariableLiteral var = (LLVMVariableLiteral)this.getLhs();
            LLVMHeuristicVariable ref = state.getSimpleTermForLiteral(var);
            if (ref != null) {
                IntervalBound upper = state.getValue(ref).getThisAsAbstractBoundedInt().getUpper();
                if (!upper.isFinite()) {
                    return false;
                }
                varToVal.put(var, upper.getConstant());
            } else {
                return false;
            }
        }
        if (this.getRhs() instanceof LLVMVariableLiteral) {
            LLVMVariableLiteral var = (LLVMVariableLiteral)this.getRhs();
            LLVMHeuristicVariable ref = state.getSimpleTermForLiteral(var);
            if (ref != null) {
                IntervalBound lower = state.getValue(ref).getThisAsAbstractBoundedInt().getLower();
                if (!lower.isFinite()) {
                    return false;
                }
                varToVal.put(var, lower.getConstant());
            } else {
                return false;
            }
        }
        return this.evaluate(varToVal);
    }

    /**
     * Evaluates a relation if there are no variables.
     * @return true iff the relation holds.
     */
    public boolean evaluate() {
        switch (this.getRelationType()) {
        case EQ:
            return this.getLhs().evaluate().equals(this.getRhs().evaluate());
        case NE:
            return !this.getLhs().evaluate().equals(this.getRhs().evaluate());
        case LT:
            return this.getLhs().evaluate().compareTo(this.getRhs().evaluate()) < 0;
        case LE:
            return this.getLhs().evaluate().compareTo(this.getRhs().evaluate()) <= 0;
        default:
            // no cases left
        }
        return false;
    }

    /**
     * Evaluates a relation replacing the variables by integers.
     * @param varToVal Mapping of variables to integers.
     * @return true iff the relation holds.
     */
    public boolean evaluate(Map<LLVMLiteral, BigInteger> varToVal) {
        switch (this.getRelationType()) {
        case EQ:
            return this.getLhs().evaluate(varToVal).equals(this.getRhs().evaluate(varToVal));
        case NE:
            return !this.getLhs().evaluate(varToVal).equals(this.getRhs().evaluate(varToVal));
        case LT:
            return this.getLhs().evaluate(varToVal).compareTo(this.getRhs().evaluate(varToVal)) < 0;
        case LE:
            return this.getLhs().evaluate(varToVal).compareTo(this.getRhs().evaluate(varToVal)) <= 0;
        default:
            // no cases left
        }
        return false;
    }

    @Override
    public LLVMLiteralExpression getLhs() {
        return this.lhs;
    }

    /**
     * @return The type of this relation.
     */
    @Override
    public IntegerRelationType getRelationType() {
        return this.type;
    }

    @Override
    public LLVMLiteralExpression getRhs() {
        return this.rhs;
    }

    @Override
    @SuppressWarnings("unchecked")
    public Set<LLVMVariableLiteral> getVariables() {
        return (Set<LLVMVariableLiteral>)CompoundExpression.getVariables(this);
    }

    /**
     * Checks if a relation with concrete values holds in a state for the in the relation contained program variables,
     * using only the states' values but not its relations.
     * @param state The state to check.
     * @return True iff this relation holds in the specified state.
     */
    public boolean holdsIn(LLVMHeuristicState state) {
        Map<LLVMLiteral, BigInteger> varToVal = new LinkedHashMap<LLVMLiteral, BigInteger>();
        for (LLVMVariableLiteral var : this.getVariables()) {
            LLVMHeuristicVariable ref = state.getSimpleTermForLiteral(var);
            if (ref != null && ref.isConcrete()) {
                varToVal.put(var, ((LLVMHeuristicConstRef)ref).getIntegerValue());
            } else {
                return this.checkIntervalRelation(state);
            }
        }
        return this.evaluate(varToVal);
    }

    /**
     * @return True iff this relation is of the form lit1 relType lit2.
     */
    public boolean isSimple() {
        return this.getLhs() instanceof LLVMLiteral && this.getRhs() instanceof LLVMLiteral;
    }

    @Override
    public IntegerRelation negate() {
        return new LLVMLiteralRelation(this.getRelationType().invert(), this.getLhs(), this.getRhs());
    }

    @Override
    public IntegerRelation setLhs(FunctionalIntegerExpression lhs) {
        return new LLVMLiteralRelation(this.getRelationType(), (LLVMLiteralExpression)lhs, this.getRhs());
    }

    @Override
    public IntegerRelation setRhs(FunctionalIntegerExpression rhs) {
        return new LLVMLiteralRelation(this.getRelationType(), this.getLhs(), (LLVMLiteralExpression)rhs);
    }

    /**
     * Substitutes all occurrences of the literal oldVariable by the specified OpNode.
     * @param oldVariable Literal which will be replaced.
     * @param newNode The new node.
     * @return The substituted relation.
     */
    public LLVMLiteralRelation substitute(LLVMLiteral oldVariable, LLVMLiteral newNode) {
        return this.substituteLiterals(Collections.singletonMap(oldVariable, newNode));
    }

    /**
     * Substitutes all references in the key set of the map by their values.
     * @param oldToNew Literal mapping.
     * @return The substituted relation.
     */
    public LLVMLiteralRelation substituteLiterals(Map<LLVMLiteral, ? extends LLVMLiteral> oldToNew) {
        return
            new LLVMLiteralRelation(
                this.type,
                this.getLhs().substitute(oldToNew),
                this.getRhs().substitute(oldToNew)
            );
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getLhs());
        res.append(" ");
        res.append(this.type);
        res.append(" ");
        res.append(this.getRhs());
        return res.toString();
    }

    /**
     * Transforms a BasicLiteralRelation to a LLVMHeuristicRelation.
     * @param varToRef The mapping of program literals to symbolic variables.
     * @param factory The factory to build LLVMHeuristicRelations.
     * @return The relation where BasicVariableNames are substituted by LLVMHeuristicVariables.
     */
    public LLVMHeuristicRelation transformToLLVMHeuristicRelation(
        Map<LLVMVariableLiteral, LLVMHeuristicVariable> varToRef,
        LLVMHeuristicRelationFactory factory
    ) {
        LLVMHeuristicTerm left = this.getLhs().transformToLLVMHeuristicTerm(varToRef, factory.getTermFactory());
        LLVMHeuristicTerm right = this.getRhs().transformToLLVMHeuristicTerm(varToRef, factory.getTermFactory());
        if (left != null && right != null) {
            return factory.createRelation(this.getRelationType(), left, right);
        } else {
            return null;
        }
    }

}
