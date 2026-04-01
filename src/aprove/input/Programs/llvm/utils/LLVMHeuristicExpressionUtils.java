package aprove.input.Programs.llvm.utils;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Functionality for processing heuristic LLVM expressions.
 * @author cryingshadow
 * @version $Id$
 */
public abstract class LLVMHeuristicExpressionUtils {

    /**
     * @param equation Some equation.
     * @param allocations The allocations.
     * @return A pair of the two expressions lower + ref and 1 + upper if the equation is of the form
     *         lower + ref = 1 + upper for some allocation (lower,upper). Null otherwise.
     */
    public static Pair<LLVMHeuristicTerm, LLVMHeuristicTerm> checkAllocationEquation(
        LLVMHeuristicRelation equation,
        ImmutableList<LLVMAllocation> allocations
    ) {
        LLVMHeuristicTerm lhs = equation.getLhs();
        LLVMHeuristicTerm rhs = equation.getRhs();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = lhs.toLinear();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rhs.toLinear();
        if (
            lhsLinear.x instanceof LLVMHeuristicVarRef
            && lhsLinear.z.compareTo(BigInteger.ONE) == 0
            && lhsLinear.y.compareTo(BigInteger.ONE) == 0
            && rhsLinear.x instanceof LLVMHeuristicOperation
            && rhsLinear.z.compareTo(BigInteger.ONE) == 0
            && rhsLinear.y.compareTo(BigInteger.ZERO) == 0
        ) {
            LLVMHeuristicOperation op = (LLVMHeuristicOperation)rhsLinear.x;
            LLVMHeuristicTerm opLhs = op.getLhs();
            LLVMHeuristicTerm opRhs = op.getRhs();
            if (
                !(
                    op.getOperation() == ArithmeticOperationType.ADD
                    && opLhs instanceof LLVMHeuristicVarRef
                    && opRhs instanceof LLVMHeuristicVarRef
                )
            ) {
                return null;
            }
            for (LLVMAllocation allocation : allocations) {
                if (!allocation.y.equals(lhsLinear.x)) {
                    continue;
                }
                if (allocation.x.equals(opLhs) || allocation.x.equals(opRhs)) {
                    return new Pair<LLVMHeuristicTerm, LLVMHeuristicTerm>(rhs, lhs);
                }
                return null;
            }
        } else if (
            rhsLinear.x instanceof LLVMHeuristicVarRef
            && rhsLinear.z.compareTo(BigInteger.ONE) == 0
            && rhsLinear.y.compareTo(BigInteger.ONE) == 0
            && lhsLinear.x instanceof LLVMHeuristicOperation
            && lhsLinear.z.compareTo(BigInteger.ONE) == 0
            && lhsLinear.y.compareTo(BigInteger.ZERO) == 0
        ) {
            LLVMHeuristicOperation op = (LLVMHeuristicOperation)lhsLinear.x;
            LLVMHeuristicTerm opLhs = op.getLhs();
            LLVMHeuristicTerm opRhs = op.getRhs();
            if (
                !(
                    op.getOperation() == ArithmeticOperationType.ADD
                    && opLhs instanceof LLVMHeuristicVarRef
                    && opRhs instanceof LLVMHeuristicVarRef
                )
            ) {
                return null;
            }
            for (LLVMAllocation allocation : allocations) {
                if (!allocation.y.equals(rhsLinear.x)) {
                    continue;
                }
                if (allocation.x.equals(opLhs) || allocation.x.equals(opRhs)) {
                    return new Pair<LLVMHeuristicTerm, LLVMHeuristicTerm>(lhs, rhs);
                }
                return null;
            }
        }
        return null;
    }

    /**
     * @param expr The expression.
     * @param refs A set of references.
     * @return A reference from the specified set which is the only reference from that set occurring in the specified
     *         expression and it occurs exactly once and the factor by which this reference is multiplied within the
     *         expression. Null if no such reference exists.
     */
    public static Pair<LLVMHeuristicVariable, BigInteger> exactlyOneOccurrence(
        LLVMHeuristicTerm expr,
        Set<LLVMHeuristicVariable> refs
    ) {
        return LLVMHeuristicExpressionUtils.exactlyOneOccurrence(expr, refs, BigInteger.ONE);
    }

    /**
     * TODO: This is just a pattern matching heuristic. Would real inference be better (precision vs. runtime)?
     * @param values The value function.
     * @param rels The known relations.
     * @param expr An expression.
     * @return A reference equating the specified expression in the relations of this set. Null if no such reference
     *         can be found.
     */
    public static LLVMHeuristicVariable findReferenceForExpression(
        ImmutableMap<LLVMHeuristicVariable, LLVMValue> values,
        LLVMHeuristicRelationSet rels,
        LLVMHeuristicTerm expr
    ) {
        if (expr instanceof LLVMHeuristicVariable) {
            return (LLVMHeuristicVariable)expr;
        } else if (expr == null) {
            return null;
        }
        final int limit = rels.computeMaximalNumberOfVariableOccurrences();
        // set of equal expressions to the original one
        final Set<Triple<LLVMHeuristicTerm, BigInteger, BigInteger>> equal =
            new LinkedHashSet<Triple<LLVMHeuristicTerm, BigInteger, BigInteger>>();
        final Set<Triple<LLVMHeuristicTerm, BigInteger, BigInteger>> newEqual =
            new LinkedHashSet<Triple<LLVMHeuristicTerm, BigInteger, BigInteger>>();
        newEqual.add(expr.toLinear());
        final LLVMHeuristicTermFactory termFactory = LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY;
        while (!newEqual.isEmpty()) {
            equal.addAll(newEqual);
            final Set<Triple<LLVMHeuristicTerm, BigInteger, BigInteger>> oldEqual =
                new LinkedHashSet<Triple<LLVMHeuristicTerm, BigInteger, BigInteger>>(newEqual);
            newEqual.clear();
            for (LLVMHeuristicRelation rel : rels.getEquations()) {
                final Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = rel.getLhs().toLinear();
                final Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rel.getRhs().toLinear();
                for (Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear : oldEqual) {
                    if (linear.x.equals(lhsLinear.x) && linear.z.compareTo(lhsLinear.z) == 0) {
                        // lhsLinear.y + linear.z * linear.x = rhsLinear.y + rhsLinear.z * rhsLinear.x
                        // linear.y + linear.z * linear.x = (linear.y - lhsLinear.y) + lhsLinear.y + linear.z * linear.x
                        // = (linear.y - lhsLinear.y) + rhsLinear.y + rhsLinear.z * rhsLinear.x
                        final BigInteger offset = rhsLinear.y.add(linear.y).subtract(lhsLinear.y);
                        if (
                            rhsLinear.x instanceof LLVMHeuristicVariable
                            && offset.compareTo(BigInteger.ZERO) == 0
                            && rhsLinear.z.compareTo(BigInteger.ONE) == 0
                        ) {
                            return (LLVMHeuristicVariable)rhsLinear.x;
                        } else if (rhsLinear.x == null) {
                            return termFactory.constant(rhsLinear.y);
                        }
                        newEqual.add(
                            new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(rhsLinear.x, offset, rhsLinear.z)
                        );
                    } else if (linear.x.equals(rhsLinear.x) && linear.z.compareTo(rhsLinear.z) == 0) {
                        // lhsLinear.y + lhsLinear.z * lhsLinear.x = rhsLinear.y + linear.z * linear.x
                        // linear.y + linear.z * linear.x = (linear.y - rhsLinear.y) + rhsLinear.y + linear.z * linear.x
                        // = (linear.y - rhsLinear.y) + lhsLinear.y + lhsLinear.z * lhsLinear.x
                        final BigInteger offset = lhsLinear.y.add(linear.y).subtract(rhsLinear.y);
                        if (
                            lhsLinear.x instanceof LLVMHeuristicVariable
                            && offset.compareTo(BigInteger.ZERO) == 0
                            && lhsLinear.z.compareTo(BigInteger.ONE) == 0
                        ) {
                            return (LLVMHeuristicVariable)lhsLinear.x;
                        } else if (lhsLinear.x == null) {
                            return termFactory.constant(lhsLinear.y);
                        }
                        newEqual.add(
                            new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(lhsLinear.x, offset, lhsLinear.z)
                        );
                    } else {
                        if (
                            lhsLinear.x instanceof LLVMHeuristicVariable
                            && (
                                rhsLinear.x == null
                                || rhsLinear.z.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) == 0
                            )
                        ) {
                            final BigInteger offset = rhsLinear.y.subtract(lhsLinear.y);
                            if (offset.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) == 0) {
                                final LLVMHeuristicTerm newExpr =
                                    linear.x.substitute(
                                        Collections.<LLVMHeuristicVariable, LLVMHeuristicTerm>singletonMap(
                                            (LLVMHeuristicVariable)lhsLinear.x,
                                            termFactory.create(
                                                rhsLinear.x,
                                                offset.divide(lhsLinear.z),
                                                rhsLinear.x == null ? null : rhsLinear.z.divide(lhsLinear.z)
                                            )
                                        )
                                    );
                                if (newExpr.getNumberOfVarOccs() < limit) {
                                    final Triple<LLVMHeuristicTerm, BigInteger, BigInteger> newLinear =
                                        newExpr.toLinear();
                                    if (newLinear.x != null) {
                                        newEqual.add(
                                            new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(
                                                newLinear.x,
                                                newLinear.y.multiply(linear.z).add(linear.y),
                                                newLinear.z.multiply(linear.z)
                                            )
                                        );
                                    }
                                }
                            }
                        }
                        if (
                            rhsLinear.x instanceof LLVMHeuristicVariable
                            && (
                                lhsLinear.x == null
                                || lhsLinear.z.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) == 0
                            )
                        ) {
                            final BigInteger offset = lhsLinear.y.subtract(rhsLinear.y);
                            if (offset.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) == 0) {
                                final LLVMHeuristicTerm newExpr =
                                    linear.x.substitute(
                                        Collections.<LLVMHeuristicVariable, LLVMHeuristicTerm>singletonMap(
                                            (LLVMHeuristicVariable)rhsLinear.x,
                                            termFactory.create(
                                                lhsLinear.x,
                                                offset.divide(rhsLinear.z),
                                                lhsLinear.x == null ? null : lhsLinear.z.divide(rhsLinear.z)
                                            )
                                        )
                                    );
                                if (newExpr.getNumberOfVarOccs() < limit) {
                                    final Triple<LLVMHeuristicTerm, BigInteger, BigInteger> newLinear =
                                        newExpr.toLinear();
                                    if (newLinear.x != null) {
                                        newEqual.add(
                                            new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(
                                                newLinear.x,
                                                newLinear.y.multiply(linear.z).add(linear.y),
                                                newLinear.z.multiply(linear.z)
                                            )
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
            newEqual.removeAll(equal);
        }
        // we did not find an equal reference yet - check remainder case
        for (Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear : equal) {
            if (
                !(linear.x instanceof LLVMHeuristicOperation)
                || linear.z.compareTo(BigInteger.ONE) != 0
                || linear.y.compareTo(BigInteger.ZERO) != 0
            ) {
                continue;
            }
            final LLVMHeuristicOperation op = (LLVMHeuristicOperation)linear.x;
            final Triple<LLVMHeuristicTerm, BigInteger, BigInteger> opLhsLinear = op.getLhs().toLinear();
            final LLVMHeuristicTerm opRhs = op.getRhs();
            if (
                op.getOperation() != ArithmeticOperationType.TMOD
                || !(opRhs instanceof LLVMHeuristicConstRef && opLhsLinear.x instanceof LLVMHeuristicVariable)
            ) {
                continue;
            }
            final AbstractInt value =
                LLVMHeuristicState.getValue((LLVMHeuristicVariable)opLhsLinear.x, values).getThisAsAbstractInt();
            if (opLhsLinear.z.compareTo(BigInteger.ONE) < 0 || !value.isNonNegative()) {
                continue;
            }
            // we have an expression of the form (opLhsLinear.y + opLhsLinear.z * opLhsLinear.x) % opRhs
            for (LLVMHeuristicRelation rel : rels.getEquations()) {
                if (rel.getNumberOfVarOccs() != 1) {
                    continue;
                }
                final LLVMHeuristicTerm lhs = rel.getLhs();
                final LLVMHeuristicTerm rhs = rel.getRhs();
                if (lhs instanceof LLVMHeuristicOperation) {
                    if (!(rhs instanceof LLVMHeuristicConstRef)) {
                        continue;
                    }
                    final LLVMHeuristicOperation relOp = (LLVMHeuristicOperation)lhs;
                    final Triple<LLVMHeuristicTerm, BigInteger, BigInteger> relOpLhsLinear = relOp.getLhs().toLinear();
                    final LLVMHeuristicTerm relOpRhs = relOp.getRhs();
                    BigInteger offset = opLhsLinear.y.subtract(relOpLhsLinear.y);
                    if (
                        !(relOp.getOperation() == ArithmeticOperationType.TMOD
                        && opRhs.equals(relOpRhs)
                        && opLhsLinear.x.equals(relOpLhsLinear.x) && opLhsLinear.z.compareTo(relOpLhsLinear.z) == 0)
                    ) {
                        continue;
                    }
                    final BigInteger c = ((LLVMHeuristicConstRef)opRhs).getIntegerValue();
                    if (offset.compareTo(BigInteger.ZERO) < 0) {
                        if (value.getLower().compareTo(offset.abs()) < 0) {
                            continue;
                        }
                        while (offset.compareTo(BigInteger.ZERO) < 0) {
                            offset = offset.add(c);
                        }
                    }
                    // we have a relation of the form (relOpLhsLinear.y + opLhsLinear.z * opLhsLinear.x) % opRhs = rhs
                    // - this implies (opLhsLinear.y + opLhsLinear.z * opLhsLinear.x) % opRhs =
                    // (((opLhsLinear.y - relOpLhsLinear.y) % opRhs) + rhs) % opRhs
                    return
                        termFactory.constant(
                            offset.remainder(c).add(((LLVMHeuristicConstRef)rhs).getIntegerValue()).remainder(c)
                        );
                } else if (rhs instanceof LLVMHeuristicOperation) {
                    if (!(lhs instanceof LLVMHeuristicConstRef)) {
                        continue;
                    }
                    final LLVMHeuristicOperation relOp = (LLVMHeuristicOperation)rhs;
                    final Triple<LLVMHeuristicTerm, BigInteger, BigInteger> relOpLhsLinear = relOp.getLhs().toLinear();
                    final LLVMHeuristicTerm relOpRhs = relOp.getRhs();
                    BigInteger offset = opLhsLinear.y.subtract(relOpLhsLinear.y);
                    if (
                        !(relOp.getOperation() == ArithmeticOperationType.TMOD
                        && opRhs.equals(relOpRhs)
                        && opLhsLinear.x.equals(relOpLhsLinear.x) && opLhsLinear.z.compareTo(relOpLhsLinear.z) == 0)
                    ) {
                        continue;
                    }
                    final BigInteger c = ((LLVMHeuristicConstRef)opRhs).getIntegerValue();
                    if (offset.compareTo(BigInteger.ZERO) < 0) {
                        if (value.getLower().compareTo(offset.abs()) < 0) {
                            continue;
                        }
                        while (offset.compareTo(BigInteger.ZERO) < 0) {
                            offset = offset.add(c);
                        }
                    }
                    // we have a relation of the form lhs = (relOpLhsLinear.y + opLhsLinear.z * opLhsLinear.x) % opRhs
                    // - this implies (opLhsLinear.y + opLhsLinear.z * opLhsLinear.x) % opRhs =
                    // (((opLhsLinear.y - relOpLhsLinear.y) % opRhs) + lhs) % opRhs
                    return
                        termFactory.constant(
                            offset.remainder(c).add(((LLVMHeuristicConstRef)lhs).getIntegerValue()).remainder(c)
                        );
                }
            }
        }
        return null;
    }
    
    /**
     * @param expr The expression.
     * @param rels Relation set.
     * @param strict Strict or weak relation?
     * @param greater Greater or less than?
     * @return The set of expressions emerging from the specified one by inequalities between values occurring in it 
     *         such that the specified expression is known to be in the desired relation to the resulting expressions 
     *         by the specified value function.
     */
    public static Set<LLVMHeuristicTerm> inRelationByInequality(
        LLVMHeuristicTerm expr,
        ImmutableSet<LLVMHeuristicRelation> rels,
        boolean strict,
        boolean greater
    ) {
        final LLVMHeuristicTermFactory termFactory = LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY;
        final LLVMHeuristicRelationFactory relFactory = LLVMHeuristicRelationFactory.LLVM_HEURISTIC_RELATION_FACTORY;
        if (!(expr instanceof LLVMHeuristicOperation)) {
            return Collections.emptySet();
        }
        // here, we know that expr is an operation
        final LLVMHeuristicOperation op = (LLVMHeuristicOperation)expr;
        final ArithmeticOperationType opType = op.getOperation();
        final LLVMHeuristicTerm lhs = op.getLhs();
        final LLVMHeuristicTerm rhs = op.getRhs();
        Set<LLVMHeuristicTerm> res = new LinkedHashSet<LLVMHeuristicTerm>();
        switch (opType) {
            case ADD:
                if (rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LE, lhs.negate(), rhs))
                    || rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LE, rhs.negate(), lhs))) {
                    if (greater) {
                        if (strict) {
                            res.add(termFactory.constant(BigInteger.ONE.negate()));
                        } else {
                            res.add(termFactory.constant(BigInteger.ZERO));
                        }
                    }
                }
                if (rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LT, lhs.negate(), rhs))
                    || rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LT, rhs.negate(), lhs))) {
                    if (greater) {
                        if (strict) {
                            res.add(termFactory.constant(BigInteger.ZERO));
                        } else {
                            res.add(termFactory.constant(BigInteger.ONE));
                        }
                    }
                }
                if (rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LE, lhs, rhs.negate()))
                    || rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LE, rhs, lhs.negate()))) {
                    if (!greater) {
                        if (strict) {
                            res.add(termFactory.constant(BigInteger.ONE));
                        } else {
                            res.add(termFactory.constant(BigInteger.ZERO));
                        }
                    }
                }
                if (rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LT, lhs, rhs.negate()))
                    || rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LT, rhs, lhs.negate()))) {
                    if (!greater) {
                        if (strict) {
                            res.add(termFactory.constant(BigInteger.ZERO));
                        } else {
                            res.add(termFactory.constant(BigInteger.ONE.negate()));
                        }
                    }
                }
                return res;
            case SUB:
                if (rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LE, lhs, rhs))
                    || rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LE, rhs.negate(), lhs.negate()))) {
                    if (!greater) {
                        if (strict) {
                            res.add(termFactory.constant(BigInteger.ONE));
                        } else {
                            res.add(termFactory.constant(BigInteger.ZERO));
                        }
                    }
                }
                if (rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LT, lhs, rhs))
                    || rels.contains(relFactory.createRelation(LLVMHeuristicRelationType.LT, rhs.negate(), lhs.negate()))) {
                    if (!greater) {
                        if (strict) {
                            res.add(termFactory.constant(BigInteger.ZERO));
                        } else {
                            res.add(termFactory.constant(BigInteger.ONE.negate()));
                        }
                    }
                }
                return res;
            default:
                return Collections.emptySet();
        }
    }

    /**
     * @param expr The expression.
     * @param values Value function.
     * @param strict Strict or weak relation?
     * @param greater Greater or less than?
     * @return The set of expressions emerging from the specified one by replacing some refs by extreme constants such
     *         that the specified expression is known to be in the desired relation to the resulting expressions by the
     *         specified value function.
     */
    public static Set<LLVMHeuristicTerm> inRelationByReplacingRefsByConstants(
        LLVMHeuristicTerm expr,
        ImmutableMap<LLVMHeuristicVariable, LLVMValue> values,
        boolean strict,
        boolean greater
    ) {
        final LLVMHeuristicTermFactory termFactory = LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY;
        if (expr instanceof LLVMHeuristicConstRef) {
            return Collections.emptySet();
        } else if (expr instanceof LLVMHeuristicVarRef) {
            if (!values.containsKey(expr)) {
                return Collections.emptySet();
            }
            // TODO the following statement will lead to a cast exception as soon as we have other value types than
            // integers
            AbstractBoundedInt val =
                LLVMHeuristicState.getValue((LLVMHeuristicVariable)expr, values).getThisAsAbstractBoundedInt();
            if (greater) {
                // the variable is greater than its lowest value - 1
                IntervalBound smallest = val.getLower();
                if (!smallest.isFinite()) {
                    return Collections.emptySet();
                }
                BigInteger res = smallest.getConstant();
                if (strict) {
                    res = res.subtract(BigInteger.ONE);
                }
                return Collections.<LLVMHeuristicTerm>singleton(termFactory.constant(res));
            } else {
                // the variable is less than its biggest value + 1
                IntervalBound biggest = val.getUpper();
                if (!biggest.isFinite()) {
                    return Collections.emptySet();
                }
                BigInteger res = biggest.getConstant();
                if (strict) {
                    res = res.add(BigInteger.ONE);
                }
                return Collections.<LLVMHeuristicTerm>singleton(termFactory.constant(res));
            }
        }
        // here, we know that expr is an operation
        final LLVMHeuristicOperation op = (LLVMHeuristicOperation)expr;
        final ArithmeticOperationType opType = op.getOperation();
        final LLVMHeuristicTerm lhs = op.getLhs();
        final LLVMHeuristicTerm rhs = op.getRhs();
        Set<LLVMHeuristicTerm> res = new LinkedHashSet<LLVMHeuristicTerm>();
        switch (opType) {
            case ADD:
                LLVMHeuristicExpressionUtils.addReplacedAdditiveCombinations(
                    op,
                    res,
                    LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(lhs, values, false, greater),
                    LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(rhs, values, false, greater),
                    strict,
                    greater
                );
                return res;
            case SUB:
                LLVMHeuristicExpressionUtils.addReplacedAdditiveCombinations(
                    op,
                    res,
                    LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(lhs, values, false, greater),
                    LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(rhs, values, false, !greater),
                    strict,
                    greater
                );
                return res;
            case MUL:
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> origLeftLinear = lhs.toLinear();
                if (origLeftLinear.x == null) {
                    if (origLeftLinear.y.compareTo(BigInteger.ZERO) > 0) {
                        for (
                            LLVMHeuristicTerm rightExpr :
                                LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(rhs, values, false, greater)
                        ) {
                            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> repRightLinear = rightExpr.toLinear();
                            if (repRightLinear.x == null) {
                                // this yields a constant
                                BigInteger offset = repRightLinear.y.multiply(origLeftLinear.y);
                                if (strict) {
                                    if (greater) {
                                        offset = offset.subtract(BigInteger.ONE);
                                    } else {
                                        offset = offset.add(BigInteger.ONE);
                                    }
                                }
                                res.add(termFactory.constant(offset));
                            } else {
                                BigInteger offset = repRightLinear.y.multiply(origLeftLinear.y);
                                if (strict) {
                                    if (greater) {
                                        offset = offset.subtract(BigInteger.ONE);
                                    } else {
                                        offset = offset.add(BigInteger.ONE);
                                    }
                                }
                                res.add(
                                    termFactory.create(
                                        ArithmeticOperationType.ADD,
                                        termFactory.constant(offset),
                                        termFactory.create(
                                            ArithmeticOperationType.MUL,
                                            termFactory.constant(origLeftLinear.y.multiply(repRightLinear.z)),
                                            repRightLinear.x
                                        )
                                    )
                                );
                            }
                        }
                    } else if (origLeftLinear.y.compareTo(BigInteger.ZERO) < 0) {
                        for (
                            LLVMHeuristicTerm rightExpr :
                                LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(rhs, values, false, !greater)
                        ) {
                            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> repRightLinear = rightExpr.toLinear();
                            if (repRightLinear.x == null) {
                                // this yields a constant
                                BigInteger offset = repRightLinear.y.multiply(origLeftLinear.y);
                                if (strict) {
                                    if (greater) {
                                        offset = offset.subtract(BigInteger.ONE);
                                    } else {
                                        offset = offset.add(BigInteger.ONE);
                                    }
                                }
                                res.add(termFactory.constant(offset));
                            } else {
                                BigInteger offset = repRightLinear.y.multiply(origLeftLinear.y);
                                if (strict) {
                                    if (greater) {
                                        offset = offset.subtract(BigInteger.ONE);
                                    } else {
                                        offset = offset.add(BigInteger.ONE);
                                    }
                                }
                                res.add(
                                    termFactory.create(
                                        ArithmeticOperationType.ADD,
                                        termFactory.constant(offset),
                                        termFactory.create(
                                            ArithmeticOperationType.MUL,
                                            termFactory.constant(origLeftLinear.y.multiply(repRightLinear.z)),
                                            repRightLinear.x
                                        )
                                    )
                                );
                            }
                        }
                    } else {
                        return Collections.emptySet();
                    }
                } else if (lhs.isPositive(values)) {
                    for (
                        LLVMHeuristicTerm rightExpr :
                            LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(rhs, values, false, greater)
                    ) {
                        LLVMHeuristicTerm toAdd = termFactory.create(opType, lhs, rightExpr);
                        if (strict) {
                            toAdd = LLVMHeuristicExpressionUtils.decrement(toAdd, greater);
                        }
                        res.add(toAdd);
                    }
                } else if (lhs.isNegative(values)) {
                    for (
                        LLVMHeuristicTerm rightExpr :
                            LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(rhs, values, false, !greater)
                    ) {
                        LLVMHeuristicTerm toAdd = termFactory.create(opType, lhs, rightExpr);
                        if (strict) {
                            toAdd = LLVMHeuristicExpressionUtils.decrement(toAdd, greater);
                        }
                        res.add(toAdd);
                    }
                } else if (!strict && lhs.isNonNegative(values)) {
                    for (
                        LLVMHeuristicTerm rightExpr :
                            LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(rhs, values, false, greater)
                    ) {
                        res.add(termFactory.create(opType, lhs, rightExpr));
                    }
                } else if (!strict && lhs.isNonPositive(values)) {
                    for (
                        LLVMHeuristicTerm rightExpr :
                            LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(rhs, values, false, !greater)
                    ) {
                        res.add(termFactory.create(opType, lhs, rightExpr));
                    }
                }
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> origRightLinear = rhs.toLinear();
                if (origRightLinear.x == null) {
                    if (origRightLinear.y.compareTo(BigInteger.ZERO) > 0) {
                        for (
                            LLVMHeuristicTerm leftExpr :
                                LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(lhs, values, false, greater)
                        ) {
                            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> repLeftLinear = leftExpr.toLinear();
                            if (repLeftLinear.x == null) {
                                // this yields a constant
                                BigInteger offset = repLeftLinear.y.multiply(origRightLinear.y);
                                if (strict) {
                                    if (greater) {
                                        offset = offset.subtract(BigInteger.ONE);
                                    } else {
                                        offset = offset.add(BigInteger.ONE);
                                    }
                                }
                                res.add(termFactory.constant(offset));
                            } else {
                                BigInteger offset = repLeftLinear.y.multiply(origRightLinear.y);
                                if (strict) {
                                    if (greater) {
                                        offset = offset.subtract(BigInteger.ONE);
                                    } else {
                                        offset = offset.add(BigInteger.ONE);
                                    }
                                }
                                res.add(
                                    termFactory.create(
                                        ArithmeticOperationType.ADD,
                                        termFactory.constant(offset),
                                        termFactory.create(
                                            ArithmeticOperationType.MUL,
                                            termFactory.constant(origRightLinear.y.multiply(repLeftLinear.z)),
                                            repLeftLinear.x
                                        )
                                    )
                                );
                            }
                        }
                    } else if (origRightLinear.y.compareTo(BigInteger.ZERO) < 0) {
                        for (
                            LLVMHeuristicTerm leftExpr :
                                LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(lhs, values, false, !greater)
                        ) {
                            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> repLeftLinear = leftExpr.toLinear();
                            if (repLeftLinear.x == null) {
                                // this yields a constant
                                BigInteger offset = repLeftLinear.y.multiply(origRightLinear.y);
                                if (strict) {
                                    if (greater) {
                                        offset = offset.subtract(BigInteger.ONE);
                                    } else {
                                        offset = offset.add(BigInteger.ONE);
                                    }
                                }
                                res.add(termFactory.constant(offset));
                            } else {
                                BigInteger offset = repLeftLinear.y.multiply(origRightLinear.y);
                                if (strict) {
                                    if (greater) {
                                        offset = offset.subtract(BigInteger.ONE);
                                    } else {
                                        offset = offset.add(BigInteger.ONE);
                                    }
                                }
                                res.add(
                                    termFactory.create(
                                        ArithmeticOperationType.ADD,
                                        termFactory.constant(offset),
                                        termFactory.create(
                                            ArithmeticOperationType.MUL,
                                            termFactory.constant(origRightLinear.y.multiply(repLeftLinear.z)),
                                            repLeftLinear.x
                                        )
                                    )
                                );
                            }
                        }
                    } else {
                        return Collections.emptySet();
                    }
                } else if (rhs.isPositive(values)) {
                    for (
                        LLVMHeuristicTerm leftExpr :
                            LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(lhs, values, false, greater)
                    ) {
                        LLVMHeuristicTerm toAdd = termFactory.create(opType, leftExpr, rhs);
                        if (strict) {
                            toAdd = LLVMHeuristicExpressionUtils.decrement(toAdd, greater);
                        }
                        res.add(toAdd);
                    }
                } else if (rhs.isNegative(values)) {
                    for (
                        LLVMHeuristicTerm leftExpr :
                            LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(lhs, values, false, !greater)
                    ) {
                        LLVMHeuristicTerm toAdd = termFactory.create(opType, leftExpr, rhs);
                        if (strict) {
                            toAdd = LLVMHeuristicExpressionUtils.decrement(toAdd, greater);
                        }
                        res.add(toAdd);
                    }
                } else if (!strict && rhs.isNonNegative(values)) {
                    for (
                        LLVMHeuristicTerm leftExpr :
                            LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(lhs, values, false, greater)
                    ) {
                        res.add(termFactory.create(opType, leftExpr, rhs));
                    }
                } else if (!strict && rhs.isNonPositive(values)) {
                    for (
                        LLVMHeuristicTerm leftExpr :
                            LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(lhs, values, false, !greater)
                    ) {
                        res.add(termFactory.create(opType, leftExpr, rhs));
                    }
                }
                return res;
            case TMOD:
                if (rhs instanceof LLVMHeuristicConstRef) {
                    if (greater) {
                        if (lhs.isNonNegative(values)) {
                            return
                                Collections.<LLVMHeuristicTerm>singleton(
                                    termFactory.constant(strict ? IntegerUtils.NEGONE : BigInteger.ZERO)
                                );
                        } else {
                            return
                                Collections.<LLVMHeuristicTerm>singleton(
                                    termFactory.constant(
                                        ((LLVMHeuristicConstRef)rhs).getIntegerValue().abs().negate().add(
                                            strict ? BigInteger.ZERO : BigInteger.ONE
                                        )
                                    )
                                );
                        }
                    } else {
                        if (lhs.isNonPositive(values)) {
                            return
                                Collections.<LLVMHeuristicTerm>singleton(
                                    termFactory.constant(strict ? BigInteger.ONE : BigInteger.ZERO)
                                );
                        } else {
                            return
                                Collections.<LLVMHeuristicTerm>singleton(
                                    termFactory.constant(
                                        ((LLVMHeuristicConstRef)rhs).getIntegerValue().abs().subtract(
                                            strict ? BigInteger.ZERO : BigInteger.ONE
                                        )
                                    )
                                );
                        }
                    }
                }
                return Collections.emptySet();
            default:
                return Collections.emptySet();
        }
    }

    /**
     * Updates the old replacement map by the new replacement map (and checks consistency if assertions are turned on).
     * @param oldReplacements The old replacements.
     * @param newReplacements The new replacements.
     */
    public static void updateReplacements(
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> oldReplacements,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> newReplacements
    ) {
        for (Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> oldEntry : oldReplacements.entrySet()) {
            LLVMHeuristicVariable value = oldEntry.getValue();
            if (newReplacements.containsKey(value)) {
                oldEntry.setValue(newReplacements.get(value));
            }
            if (Globals.useAssertions) {
                LLVMHeuristicVariable key = oldEntry.getKey();
                if (newReplacements.containsKey(key)) {
                    assert (newReplacements.get(key).equals(oldEntry.getValue())) : "Inconsistent replacement!";
                }
            }
        }
        oldReplacements.putAll(newReplacements);
    }

    /**
     * Adds all combinations of replaced expressions for the left- and right-hand side of an additive expression to the
     * specified res set.
     * @param op The additive expression.
     * @param res The set to add the replaced expressions to.
     * @param left The expressions to replace the left-hand side with.
     * @param right The expressions to replace the right-hand side with.
     * @param strict Strict relation?
     * @param greater Greater relation?
     */
    private static void addReplacedAdditiveCombinations(
        LLVMHeuristicOperation op,
        Set<LLVMHeuristicTerm> res,
        Set<LLVMHeuristicTerm> left,
        Set<LLVMHeuristicTerm> right,
        boolean strict,
        boolean greater
    ) {
        final LLVMHeuristicTermFactory termFactory = LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY;
        final ArithmeticOperationType opType = op.getOperation();
        if (Globals.useAssertions) {
            assert (opType == ArithmeticOperationType.ADD || opType == ArithmeticOperationType.SUB) :
                "This method should only be called on additive expressions!";
        }
        final LLVMHeuristicTerm lhs = op.getLhs();
        final LLVMHeuristicTerm rhs = op.getRhs();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> origLeftLinear = lhs.toLinear();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> origRightLinear = rhs.toLinear();
        for (LLVMHeuristicTerm leftExpr : left) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> repLeftLinear = leftExpr.toLinear();
            if (repLeftLinear.x == null && origRightLinear.x == null) {
                // this yields a constant
                BigInteger constant;
                switch (opType) {
                    case ADD:
                        constant = repLeftLinear.y.add(origRightLinear.y);
                        break;
                    case SUB:
                        constant = repLeftLinear.y.subtract(origRightLinear.y);
                        break;
                    default:
                        throw new IllegalStateException("This method should only be called on additive expressions!");
                }
                if (strict) {
                    if (greater) {
                        constant = constant.subtract(BigInteger.ONE);
                    } else {
                        constant = constant.add(BigInteger.ONE);
                    }
                }
                res.add(termFactory.constant(constant));
            } else {
                LLVMHeuristicTerm toAdd = termFactory.create(opType, leftExpr, rhs);
                if (strict) {
                    toAdd = LLVMHeuristicExpressionUtils.decrement(toAdd, greater);
                }
                res.add(toAdd);
            }
            for (LLVMHeuristicTerm rightExpr : right) {
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> repRightLinear = rightExpr.toLinear();
                if (repLeftLinear.x == null && repRightLinear.x == null) {
                    // this yields a constant
                    BigInteger constant;
                    switch (opType) {
                        case ADD:
                            constant = repLeftLinear.y.add(repRightLinear.y);
                            break;
                        case SUB:
                            constant = repLeftLinear.y.subtract(repRightLinear.y);
                            break;
                        default:
                            throw new IllegalStateException(
                                "This method should only be called on additive expressions!"
                            );
                    }
                    if (strict) {
                        if (greater) {
                            constant = constant.subtract(BigInteger.ONE);
                        } else {
                            constant = constant.add(BigInteger.ONE);
                        }
                    }
                    res.add(termFactory.constant(constant));
                } else {
                    LLVMHeuristicTerm toAdd = termFactory.create(opType, leftExpr, rightExpr);
                    if (strict) {
                        toAdd = LLVMHeuristicExpressionUtils.decrement(toAdd, greater);
                    }
                    res.add(toAdd);
                }
            }
        }
        for (LLVMHeuristicTerm rightExpr : right) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> repRightLinear = rightExpr.toLinear();
            if (origLeftLinear.x == null && repRightLinear.x == null) {
                // this yields a constant
                BigInteger constant;
                switch (opType) {
                    case ADD:
                        constant = origLeftLinear.y.add(repRightLinear.y);
                        break;
                    case SUB:
                        constant = origLeftLinear.y.subtract(repRightLinear.y);
                        break;
                    default:
                        throw new IllegalStateException("This method should only be called on additive expressions!");
                }
                if (strict) {
                    if (greater) {
                        constant = constant.subtract(BigInteger.ONE);
                    } else {
                        constant = constant.add(BigInteger.ONE);
                    }
                }
                res.add(termFactory.constant(constant));
            } else {
                LLVMHeuristicTerm toAdd = termFactory.create(opType, lhs, rightExpr);
                if (strict) {
                    toAdd = LLVMHeuristicExpressionUtils.decrement(toAdd, greater);
                }
                res.add(toAdd);
            }
        }
    }

    /**
     * @param term Some term.
     * @param greater Should the decrement lead to a smaller term (true) or a greater term (false)?
     * @return The specified term decremented in the specified direction.
     */
    private static LLVMHeuristicTerm decrement(LLVMHeuristicTerm term, boolean greater) {
        final LLVMHeuristicTermFactory termFactory = LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY;
        return
            termFactory.create(
                ArithmeticOperationType.ADD,
                greater ? termFactory.negone() : termFactory.one(),
                term
            );
    }

    /**
     * @param expr The expression.
     * @param refs A set of references.
     * @param factor The factor by which this expression is multiplied.
     * @return A reference from the specified set which is the only reference from that set occurring in the specified
     *         linear expression and it occurs exactly once and the factor by which this reference is multiplied within
     *         the expression. Null if no such reference exists or the expression is not linear.
     */
    private static Pair<LLVMHeuristicVariable, BigInteger> exactlyOneOccurrence(
        LLVMHeuristicTerm expr,
        Set<LLVMHeuristicVariable> refs,
        BigInteger factor
    ) {
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear = expr.toLinear();
        if (refs.contains(linear.x)) {
            return new Pair<LLVMHeuristicVariable, BigInteger>((LLVMHeuristicVariable)linear.x, factor.multiply(linear.z));
        } else if (linear.x instanceof LLVMHeuristicVariable) {
            return null;
        }
        LLVMHeuristicOperation op = (LLVMHeuristicOperation)linear.x;
        ArithmeticOperationType opType = op.getOperation();
        if (opType != ArithmeticOperationType.ADD && opType != ArithmeticOperationType.SUB) {
            return null;
        }
        Pair<LLVMHeuristicVariable, BigInteger> left =
            LLVMHeuristicExpressionUtils.exactlyOneOccurrence(op.getLhs(), refs, factor.multiply(linear.z));
        Pair<LLVMHeuristicVariable, BigInteger> right =
            LLVMHeuristicExpressionUtils.exactlyOneOccurrence(op.getRhs(), refs, factor.multiply(linear.z));
        if (left == null) {
            return right;
        } else if (right == null) {
            return left;
        } else {
            return null;
        }
    }

    /**
     * Hides default constructor.
     */
    private LLVMHeuristicExpressionUtils() {
        throw new UnsupportedOperationException("Do not instantiate me!");
    }


}
