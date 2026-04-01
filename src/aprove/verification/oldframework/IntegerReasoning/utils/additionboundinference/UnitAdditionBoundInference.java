package aprove.verification.oldframework.IntegerReasoning.utils.additionboundinference;

import java.math.*;
import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.octagondomain.*;
import aprove.verification.oldframework.IntegerReasoning.utils.boundinference.*;

/**
 * In order to effectively use the octagon domain (see {@link OctagonInterface}),
 * we need to decide if a given relation implies a relation of the form
 * (-)x + (-)y <= c, for some variables x and y and some constant c, since only
 * constraints of this form can be tracked using the octagon domain.
 *
 * We call such relations unit addition bounds, or simply addition bounds,
 * if the context is clear.
 *
 * This class encapsulates the inference of relations of such a form. However,
 * we only infer difference bounds where x != y, since, if x = y, the addition
 * bound devolves to a simple bound on a variable. This case can also be handled
 * by {@link BoundInference}, so we avoid code (and reasoning) duplication by
 * excluding that case here.
 *
 * @author Alexander Weinert
 */
public class UnitAdditionBoundInference extends IntegerRelationVisitor {

    public static Collection<UnitAdditionBound> inferUnitAdditionBounds(final IntegerRelation relation) {
        final UnitAdditionBoundInference inference = new UnitAdditionBoundInference();
        inference.visit(relation);
        return inference.result;
    }

    private BigInteger offset;

    private Collection<UnitAdditionBound> result;

    private List<UnitVariable> unitVariables;

    @Override
    public void visitEqualsRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        this.result = new HashSet<>();
        final UnitAdditionBound.Builder upperBuilder = new UnitAdditionBound.Builder();
        if (this.unitVariables.get(0).isNegated()) {
            upperBuilder.addNegatedVariable(this.unitVariables.get(0).getVariable());
        } else {
            upperBuilder.addVariable(this.unitVariables.get(0).getVariable());
        }
        if (this.unitVariables.get(1).isNegated()) {
            upperBuilder.addNegatedVariable(this.unitVariables.get(1).getVariable());
        } else {
            upperBuilder.addVariable(this.unitVariables.get(1).getVariable());
        }
        upperBuilder.setBound(this.offset.negate());
        this.result.add(upperBuilder.build());
        final UnitAdditionBound.Builder lowerBuilder = new UnitAdditionBound.Builder();
        if (this.unitVariables.get(0).isNegated()) {
            lowerBuilder.addVariable(this.unitVariables.get(0).getVariable());
        } else {
            lowerBuilder.addNegatedVariable(this.unitVariables.get(0).getVariable());
        }
        if (this.unitVariables.get(1).isNegated()) {
            lowerBuilder.addVariable(this.unitVariables.get(1).getVariable());
        } else {
            lowerBuilder.addNegatedVariable(this.unitVariables.get(1).getVariable());
        }
        lowerBuilder.setBound(this.offset);
        this.result.add(lowerBuilder.build());
    }

    @Override
    public void visitLessThanEqualsRelation(FunctionalIntegerExpression lhs, FunctionalIntegerExpression rhs) {
        this.result = new HashSet<>();
        final UnitAdditionBound.Builder builder = new UnitAdditionBound.Builder();
        if (this.unitVariables.get(0).isNegated()) {
            builder.addNegatedVariable(this.unitVariables.get(0).getVariable());
        } else {
            builder.addVariable(this.unitVariables.get(0).getVariable());
        }
        if (this.unitVariables.get(1).isNegated()) {
            builder.addNegatedVariable(this.unitVariables.get(1).getVariable());
        } else {
            builder.addVariable(this.unitVariables.get(1).getVariable());
        }
        builder.setBound(this.offset.negate());
        this.result.add(builder.build());
    }

    @Override
    public void visitLessThanRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        this.result = new HashSet<>();
        final UnitAdditionBound.Builder builder = new UnitAdditionBound.Builder();
        if (this.unitVariables.get(0).isNegated()) {
            builder.addNegatedVariable(this.unitVariables.get(0).getVariable());
        } else {
            builder.addVariable(this.unitVariables.get(0).getVariable());
        }
        if (this.unitVariables.get(1).isNegated()) {
            builder.addNegatedVariable(this.unitVariables.get(1).getVariable());
        } else {
            builder.addVariable(this.unitVariables.get(1).getVariable());
        }
        builder.setBound(this.offset.negate().subtract(BigInteger.ONE));
        this.result.add(builder.build());
    }

    @Override
    public void visitNotEqualsRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        // Do nothing as we cannot infer unit addition bounds from inequalities
    }

    @Override
    public boolean visitRelation(final FunctionalIntegerExpression lhs, final FunctionalIntegerExpression rhs) {
        this.result = null;
        this.unitVariables = new LinkedList<>();
        this.offset = BigInteger.ZERO;
        final LLVMHeuristicTermFactory termFactory = LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY;
        for (final FunctionalIntegerExpression lhsLiteral : termFactory.create(lhs).getLiterals()) {
            final UnitVariable unit = this.toUnitVariable(lhsLiteral);
            if (unit != null) {
                this.unitVariables.add(unit);
            } else if (lhsLiteral instanceof LLVMHeuristicConstRef) {
                this.offset = this.offset.add(((LLVMHeuristicConstRef) lhsLiteral).getIntegerValue());
            } else {
                return false;
            }
        }
        for (final FunctionalIntegerExpression rhsLiteral : termFactory.create(rhs).getLiterals()) {
            final UnitVariable unit = this.toUnitVariable(rhsLiteral.negate());
            if (unit != null) {
                this.unitVariables.add(unit);
            } else if (rhsLiteral instanceof LLVMHeuristicConstRef) {
                this.offset = this.offset.add(((LLVMHeuristicConstRef) rhsLiteral).getIntegerValue().negate());
            } else {
                return false;
            }
        }
        if (this.unitVariables.size() != 2) {
            return false;
        }
        return true;
    }

    private UnitVariable toUnitVariable(final FunctionalIntegerExpression expr) {
        if (expr instanceof LLVMHeuristicVarRef) {
            return UnitVariable.createVariable((LLVMHeuristicVarRef)expr);
        } else if (expr instanceof LLVMOperation) {
            final LLVMOperation op = (LLVMOperation)expr;
            if (op.getOperation().equals(ArithmeticOperationType.MUL)) {
                if (
                    op.getLhs() instanceof LLVMHeuristicConstRef
                    && ((LLVMHeuristicConstRef)op.getLhs()).getIntegerValue().equals(BigInteger.valueOf(-1))
                    && op.getRhs() instanceof LLVMHeuristicVarRef
                ) {
                    return UnitVariable.createNegatedVariable((LLVMHeuristicVarRef)op.getRhs());
                } else if (
                    op.getRhs() instanceof LLVMHeuristicConstRef
                    && ((LLVMHeuristicConstRef)op.getRhs()).getIntegerValue().equals(BigInteger.valueOf(-1))
                    && op.getLhs() instanceof LLVMHeuristicVarRef
                ) {
                    return UnitVariable.createNegatedVariable((LLVMHeuristicVarRef) op.getLhs());
                }
            }
        }
        return null;
    }

}
