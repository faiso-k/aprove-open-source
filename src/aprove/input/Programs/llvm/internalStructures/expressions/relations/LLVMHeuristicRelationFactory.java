package aprove.input.Programs.llvm.internalStructures.expressions.relations;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Factory for heuristic relations.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMHeuristicRelationFactory extends LLVMRelationFactory {

    /**
     * The default heuristic relation factory for LLVM.
     */
    public static final LLVMHeuristicRelationFactory LLVM_HEURISTIC_RELATION_FACTORY =
        new LLVMHeuristicRelationFactory();

    /**
     * No instantiation from outside.
     */
    private LLVMHeuristicRelationFactory() {
        // do not instantiate me from outside!
    }

    @Override
    public LLVMHeuristicRelation createAdditionRelation(
        LLVMSymbolicVariable left,
        LLVMTerm operand1,
        LLVMTerm operand2
    ) {
        return (LLVMHeuristicRelation)super.createAdditionRelation(left, operand1, operand2);
    }

    @Override
    public LLVMHeuristicRelation createAlignmentRelation(LLVMSimpleTerm ref, LLVMConstant alignment) {
        return (LLVMHeuristicRelation)super.createAlignmentRelation(ref, alignment);
    }

    /**
     * Creates a relation equivalent to rel, but handling overflows at the right hand side.
     * @param rel The original relation.
     * @param refType The type of the references.
     * @return For left = ref1 op ref2, the relation left = (((ref1 op ref2) + intervalSize/2) mod intervalSize) -
     * intervalSize/2, where intervalSize is the maximum interval size of left.
     */
    public LLVMHeuristicRelation createOverflowSafeRelation(LLVMHeuristicRelation rel, LLVMType refType) {
        if (Globals.useAssertions) {
            assert (rel.isSimpleArithmeticEquation()) : "We can only create simple overflow safe relations.";
        }
        LLVMHeuristicVariable left;
        LLVMHeuristicVariable ref1;
        LLVMHeuristicVariable ref2;
        ArithmeticOperationType arithType;
        if (rel.getLhs() instanceof LLVMHeuristicVariable) {
            left = (LLVMHeuristicVariable) rel.getLhs();
            LLVMOperation operation = (LLVMOperation) rel.getRhs();
            ref1 = (LLVMHeuristicVariable) (operation).getLhs();
            ref2 = (LLVMHeuristicVariable) (operation).getRhs();
            arithType = operation.getOperation();
        } else {
            left = (LLVMHeuristicVariable) rel.getRhs();
            LLVMOperation operation = (LLVMOperation) rel.getLhs();
            ref1 = (LLVMHeuristicVariable) (operation).getLhs();
            ref2 = (LLVMHeuristicVariable) (operation).getRhs();
            arithType = operation.getOperation();
        }
        return (LLVMHeuristicRelation)this.createOverflowSafeRelation(arithType, left, ref1, ref2, refType);
    }

    @Override
    public LLVMHeuristicRelation createRelation(IntegerRelation relation) {
        if (relation instanceof LLVMHeuristicRelation) {
            return (LLVMHeuristicRelation)relation;
        }
        return (LLVMHeuristicRelation)super.createRelation(relation);
    }

    @Override
    public LLVMHeuristicRelation createRelation(
        IntegerRelationType intRel,
        LLVMTerm lhs,
        LLVMTerm rhs
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        switch (intRel) {
            case GE:
                return
                    this.createRelation(LLVMHeuristicRelationType.LE, termFactory.create(rhs), termFactory.create(lhs));
            case GT:
                return
                    this.createRelation(LLVMHeuristicRelationType.LT, termFactory.create(rhs), termFactory.create(lhs));
            case LE:
                return
                    this.createRelation(LLVMHeuristicRelationType.LE, termFactory.create(lhs), termFactory.create(rhs));
            case LT:
                return
                    this.createRelation(LLVMHeuristicRelationType.LT, termFactory.create(lhs), termFactory.create(rhs));
            case EQ:
                return
                    this.createRelation(LLVMHeuristicRelationType.EQ, termFactory.create(lhs), termFactory.create(rhs));
            case NE:
                return
                    this.createRelation(LLVMHeuristicRelationType.NE, termFactory.create(lhs), termFactory.create(rhs));
            default:
                // this point should never be reached
                throw new IllegalStateException("Someone found a new way to relate integers.");
        }
    }

    /**
     * @param type The relation type.
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return A relation encoding "<code>lhs type rhs</code> (if <code>type</code> was &gt; or &gt;=, it is replaced
     *         by &lt; (resp. &lt;=) and the roles of lhs and rhs are switched).
     */
    public LLVMHeuristicRelation createRelation(
        LLVMHeuristicRelationType type,
        LLVMHeuristicTerm lhs,
        LLVMHeuristicTerm rhs
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getTermFactory();
        if (type == LLVMHeuristicRelationType.NE) {
            return new LLVMHeuristicRelation(type, lhs, rhs);
        } else {
            // the list of literals might be immutable
            List<LLVMHeuristicTerm> literals = new ArrayList<LLVMHeuristicTerm>(lhs.getLiterals());
            for (LLVMHeuristicTerm literal : rhs.getLiterals()) {
                literals.add(literal.negate());
            }
            LLVMHeuristicTerm newLhs = termFactory.zero();
            LLVMHeuristicTerm newRhs = termFactory.zero();
            for (LLVMHeuristicTerm literal : termFactory.joinMultiplicitiesOfLiterals(literals)) {
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear = literal.toLinear();
                if (linear.x == null) {
                    if (linear.y.compareTo(BigInteger.ZERO) < 0) {
                        newRhs =
                            termFactory.create(
                                ArithmeticOperationType.ADD,
                                termFactory.constant(linear.y.negate()),
                                newRhs
                            );
                    } else {
                        newLhs =
                            termFactory.create(ArithmeticOperationType.ADD, termFactory.constant(linear.y), newLhs);
                    }
                } else {
                    if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                        assert (linear.y.compareTo(BigInteger.ZERO) == 0) : "This should be another literal!";
                    }
                    if (linear.z.compareTo(BigInteger.ZERO) < 0) {
                        if (linear.z.compareTo(IntegerUtils.NEGONE) == 0) {
                            newRhs = termFactory.create(ArithmeticOperationType.ADD, newRhs, linear.x);
                        } else {
                            newRhs =
                                termFactory.create(
                                    ArithmeticOperationType.ADD,
                                    newRhs,
                                    termFactory.create(
                                        ArithmeticOperationType.MUL,
                                        termFactory.constant(linear.z.negate()),
                                        linear.x
                                    )
                                );
                        }
                    } else if (linear.z.compareTo(BigInteger.ONE) == 0) {
                        newLhs = termFactory.create(ArithmeticOperationType.ADD, newLhs, linear.x);
                    } else {
                        newLhs =
                            termFactory.create(
                                ArithmeticOperationType.ADD,
                                newLhs,
                                termFactory.create(
                                    ArithmeticOperationType.MUL,
                                    termFactory.constant(linear.z),
                                    linear.x
                                )
                            );
                    }
                }
            }
            return new LLVMHeuristicRelation(type, newLhs, newRhs);
        }
    }

    @Override
    public LLVMHeuristicRelation equalTo(LLVMTerm lhs, LLVMTerm rhs) {
        return (LLVMHeuristicRelation)super.equalTo(lhs, rhs);
    }

    @Override
    public LLVMHeuristicTermFactory getTermFactory() {
        return LLVMHeuristicTermFactory.LLVM_HEURISTIC_TERM_FACTORY;
    }

    @Override
    public LLVMHeuristicRelation lessThan(LLVMTerm lhs, LLVMTerm rhs) {
        return (LLVMHeuristicRelation)super.lessThan(lhs, rhs);
    }

    @Override
    public LLVMHeuristicRelation lessThanEquals(LLVMTerm lhs, LLVMTerm rhs) {
        return (LLVMHeuristicRelation)super.lessThanEquals(lhs, rhs);
    }

    @Override
    public LLVMHeuristicRelation notEqualTo(LLVMTerm lhs, LLVMTerm rhs) {
        return (LLVMHeuristicRelation)super.notEqualTo(lhs, rhs);
    }

}
