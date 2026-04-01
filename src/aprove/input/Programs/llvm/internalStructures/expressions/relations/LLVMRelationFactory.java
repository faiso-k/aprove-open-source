package aprove.input.Programs.llvm.internalStructures.expressions.relations;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Creates relations.
 * @author cryingshadow, Alexander Weinert
 * @version $Id$
 */
public abstract class LLVMRelationFactory {

    /**
     * @param left The left-hand side of the equation.
     * @param pVar The mandatory first part of the right-hand side of the equation.
     * @param operands The operands added to pVar in form of references and multipliers (which have to be multiplied).
     * @return an equation lhs = pVar + operand_1 + operand_2 + ... + operand_n
     */
    public LLVMRelation createAdditionRelation(
        LLVMSymbolicVariable left,
        LLVMSymbolicVariable pVar,
        List<Pair<LLVMSymbolicVariable, LLVMConstant>> operands
    ) {
        if (Globals.useAssertions) {
            assert (operands.size() > 0) : "There must be at least one operand.";
        }
        Pair<LLVMSymbolicVariable, LLVMConstant> operand = operands.get(0);
        final LLVMTermFactory termFactory = this.getTermFactory();
        LLVMTerm right = termFactory.add(pVar, termFactory.mult(operand.y, operand.x));
        for (int i = 1; i < operands.size(); i++) {
            operand = operands.get(i);
            right = termFactory.add(right, termFactory.mult(operand.y, operand.x));
        }
        return this.equalTo(left, right);
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation left = operand1 + operand2.
     */
    public LLVMRelation createAdditionRelation(LLVMSymbolicVariable left, LLVMTerm operand1, LLVMTerm operand2) {
        return this.equalTo(left, this.getTermFactory().add(operand1, operand2));
    }

    /**
     * @param ref The reference.
     * @param alignment The alignment of the reference.
     * @return An equation ref mod alignment = 0. We use the Euclidean remainder as this is supported by SMT solvers
     *         directly and since the addresses for the alignment information are positive anyway, it does not matter
     *         concerning the semantics which remainder operation we choose.
     */
    public LLVMRelation createAlignmentRelation(LLVMSimpleTerm ref, LLVMConstant alignment) {
        return
            this.equalTo(
                this.getTermFactory().operation(ArithmeticOperationType.EMOD, ref, alignment),
                this.getTermFactory().zero()
            );
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation left = operand1 & operand2.
     */
    public LLVMRelation createAndRelation(LLVMSymbolicVariable left, LLVMTerm operand1, LLVMTerm operand2) {
        return
            this.equalTo(
                left,
                this.getTermFactory().operation(ArithmeticOperationType.AND, operand1, operand2)
            );
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation left = operand1 / 2^operand2.
     */
    public LLVMRelation createArithmeticRightshiftRelation(
        LLVMSymbolicVariable left,
        LLVMSymbolicVariable operand1,
        LLVMConstant operand2
    ) {
        BigInteger val = operand2.getIntegerValue();
        if (Globals.useAssertions) {
            assert (val.bitLength() <= 31) : "Second operand is too big!";
        }
        final LLVMTermFactory termFactory = this.getTermFactory();
        return
            this.equalTo(
                left,
                termFactory.tidiv(operand1, termFactory.constant(BigInteger.valueOf(2).pow(val.intValue())))
            );
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation left = operand1 / 2^operand2.
     */
    public LLVMRelation createArithmeticRightshiftRelation(
        LLVMSymbolicVariable left,
        LLVMSymbolicVariable operand1,
        LLVMSymbolicVariable operand2
    ) {
        final LLVMTermFactory termFactory = this.getTermFactory();
        return
            this.equalTo(
                left,
                termFactory.tidiv(
                    operand1,
                    termFactory.operation(ArithmeticOperationType.POW, termFactory.constant(2), operand2)
                )
            );
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation left = operand1 / operand2.
     */
    public LLVMRelation createDivisionRelation(
        LLVMSymbolicVariable left,
        LLVMTerm operand1,
        LLVMTerm operand2
    ) {
        return this.equalTo(left, this.getTermFactory().tidiv(operand1, operand2));
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation left = operand1 * 2^operand2.
     */
    public LLVMRelation createLeftshiftRelation(
        LLVMSymbolicVariable left,
        LLVMSymbolicVariable operand1,
        LLVMConstant operand2
    ) {
        BigInteger val = operand2.getIntegerValue();
        if (Globals.useAssertions) {
            assert (val.bitLength() <= 31) : "Second operand is too big!";
        }
        final LLVMTermFactory termFactory = this.getTermFactory();
        return
            this.equalTo(
                left,
                termFactory.mult(operand1, termFactory.constant(BigInteger.valueOf(2).pow(val.intValue())))
            );
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation left = operand1 * 2^operand2.
     */
    public LLVMRelation createLeftshiftRelation(
        LLVMSymbolicVariable left,
        LLVMSymbolicVariable operand1,
        LLVMSymbolicVariable operand2
    ) {
        final LLVMTermFactory termFactory = this.getTermFactory();
        return
            this.equalTo(
                left,
                termFactory.mult(
                    operand1,
                    termFactory.operation(ArithmeticOperationType.POW, termFactory.constant(2), operand2)
                )
            );
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation lhs = operand1 * operand2.
     */
    public LLVMRelation createMultiplicationRelation(LLVMSymbolicVariable left, LLVMTerm operand1, LLVMTerm operand2) {
        return this.equalTo(left, this.getTermFactory().mult(operand1, operand2));
    }

    /**
     * Creates a relation equivalent to left = ref1 op ref2, but handling overflows on the right hand side.
     * @param arithType The type of the operator at the right hand side.
     * @param left The reference at the left hand side.
     * @param ref1 The first operand.
     * @param ref2 The second operand.
     * @param refType The type of the references.
     * @return The relation left = (((ref1 op ref2) + intervalSize/2) mod intervalSize) - intervalSize/2, where
     * intervalSize is the maximum interval size of left.
     */
    public LLVMRelation createOverflowSafeRelation(
        ArithmeticOperationType arithType,
        LLVMSymbolicVariable left,
        LLVMSymbolicVariable ref1,
        LLVMSymbolicVariable ref2,
        LLVMType refType
    ) {
        final LLVMTermFactory termFactory = this.getTermFactory();
        return
            this.equalTo(
                left,
                termFactory.sub(
                    termFactory.operation(
                        ArithmeticOperationType.EMOD,
                        termFactory.add(
                            termFactory.operation(arithType, ref1, ref2),
                            termFactory.constant(BigInteger.valueOf(2).pow(refType.size() - 1))
                        ),
                        termFactory.constant(BigInteger.valueOf(2).pow(refType.size()))
                    ),
                    termFactory.constant(BigInteger.valueOf(2).pow(refType.size() - 1))
                )
            );
    }

    /**
     * @param rel Some integer relation.
     * @return An LLVMRelation representing the specified relation.
     */
    public LLVMRelation createRelation(IntegerRelation rel) {
        if (rel instanceof LLVMRelation) {
            return (LLVMRelation)rel;
        }
        final LLVMTermFactory termFactory = this.getTermFactory();
        return
            this.createRelation(
                rel.getRelationType(),
                termFactory.create(rel.getLhs()),
                termFactory.create(rel.getRhs())
            );
    }

//    /**
//     * Creates a relation equivalent to rel, but handling overflows at the right hand side.
//     * @param rel The original relation.
//     * @param refType The type of the references.
//     * @return For left = ref1 op ref2, the relation left = (((ref1 op ref2) + intervalSize/2) mod intervalSize) -
//     * intervalSize/2, where intervalSize is the maximum interval size of left.
//     */
//    default LLVMRelation createOverflowSafeRelation(LLVMRelation rel, BasicType refType) {
//        if (Globals.useAssertions) {
//            assert (rel.isSimpleArithmeticEquation()) : "We can only create simple overflow safe relations.";
//        }
//        LLVMHeuristicVariable left;
//        LLVMHeuristicVariable ref1;
//        LLVMHeuristicVariable ref2;
//        ArithmeticOperationType arithType;
//        if (rel.getLhs() instanceof LLVMHeuristicVariable) {
//            left = (LLVMHeuristicVariable) rel.getLhs();
//            LLVMOperation operation = (LLVMOperation) rel.getRhs();
//            ref1 = (LLVMHeuristicVariable) (operation).getLhs();
//            ref2 = (LLVMHeuristicVariable) (operation).getRhs();
//            arithType = operation.getOpType();
//        } else {
//            left = (LLVMHeuristicVariable) rel.getRhs();
//            LLVMOperation operation = (LLVMOperation) rel.getLhs();
//            ref1 = (LLVMHeuristicVariable) (operation).getLhs();
//            ref2 = (LLVMHeuristicVariable) (operation).getRhs();
//            arithType = operation.getOpType();
//        }
//        return
//            new LLVMRelation(
//                HeuristicRelationType.EQ,
//                left,
//                LLVMOperation.create(
//                    ArithmeticOperationType.SUB,
//                    LLVMOperation.create(
//                        ArithmeticOperationType.MOD,
//                        LLVMOperation.create(
//                            ArithmeticOperationType.ADD,
//                            LLVMOperation.create(arithType, ref1, ref2),
//                            new LLVMHeuristicConstRef(BigInteger.valueOf(2).pow(refType.size() - 1))
//                        ),
//                        new LLVMHeuristicConstRef(BigInteger.valueOf(2).pow(refType.size()))
//                    ),
//                    new LLVMHeuristicConstRef(BigInteger.valueOf(2).pow(refType.size() - 1))
//                )
//            );
//    }

    /**
     * @param intRel The relation between lhs and rhs.
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return A relation encoding <code>lhs intRel rhs</code>.
     */
    public LLVMRelation createRelation(
        IntegerRelationType intRel,
        LLVMTerm lhs,
        LLVMTerm rhs
    ) {
        return new LLVMRelation(intRel, lhs, rhs);
    }

    /**
     * Creates a relation containing information about the gap in an interval. E.g. for [MinInt,-20] union [-5, MaxInt]
     * the relation ((x + 5) mod 2^typeSize) - 5 <= 2^typeSize - 20 is created.
     * @param ref The reference at the left hand side.
     * @param refType The refType of the reference.
     * @param innerUB The upper bound of the first interval.
     * @param innerLB The lower bound of the second interval (should be greater (!) than innerUB).
     * @return The relation ((x - innerLB) mod 2^typeSize) + innerLB <= innerUB + 2^typeSize.
     */
    public LLVMRelation createRelationForInnerBounds(
        LLVMSymbolicVariable ref,
        LLVMType refType,
        BigInteger innerUB,
        BigInteger innerLB
    ) {
        final LLVMTermFactory termFactory = this.getTermFactory();
        return
            this.lessThanEquals(
                termFactory.add(
                    termFactory.operation(
                        ArithmeticOperationType.EMOD,
                        termFactory.sub(ref, termFactory.constant(innerLB)),
                        termFactory.constant(BigInteger.valueOf(2).pow(refType.size()))
                    ),
                    termFactory.constant(innerLB)
                ),
                termFactory.add(
                    termFactory.constant(innerUB),
                    termFactory.constant(BigInteger.valueOf(2).pow(refType.size()))
                )
            );
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation lhs = operand1 % operand2. Note that the sign of the result is the sign of operand1.
     */
    public LLVMRelation createRemainderRelation(
        LLVMSymbolicVariable left,
        LLVMTerm operand1,
        LLVMTerm operand2
    ) {
        return
            this.equalTo(left, this.getTermFactory().operation(ArithmeticOperationType.TMOD, operand1, operand2));
    }

    /**
     * @param left The left-hand side of the relation.
     * @param operand1 The first operand.
     * @param operand2 The second operand.
     * @return An equation lhs = operand1 - operand2.
     */
    public LLVMRelation createSubtractionRelation(
        LLVMSymbolicVariable left,
        LLVMTerm operand1,
        LLVMTerm operand2
    ) {
        return this.equalTo(left, this.getTermFactory().sub(operand1, operand2));
    }

    /**
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return The relation lhs = rhs.
     */
    public LLVMRelation equalTo(LLVMTerm lhs, LLVMTerm rhs) {
        return this.createRelation(IntegerRelationType.EQ, lhs, rhs);
    }

    /**
     * @return The factory to produce LLVMTerms.
     */
    public LLVMTermFactory getTermFactory() {
        return LLVMDefaultTermFactory.LLVM_DEFAULT_TERM_FACTORY;
    }

    /**
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return The relation lhs < rhs.
     */
    public LLVMRelation lessThan(LLVMTerm lhs, LLVMTerm rhs) {
        return this.createRelation(IntegerRelationType.LT, lhs, rhs);
    }

    /**
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return The relation lhs <= rhs.
     */
    public LLVMRelation lessThanEquals(LLVMTerm lhs, LLVMTerm rhs) {
        return this.createRelation(IntegerRelationType.LE, lhs, rhs);
    }

    /**
     * @param term Some term.
     * @return The relation "term <= -1".
     */
    public LLVMRelation negative(LLVMTerm term) {
        return this.lessThanEquals(term, this.getTermFactory().negone());
    }

    /**
     * @param term Some term.
     * @return The relation "0 <= term".
     */
    public LLVMRelation nonNegative(LLVMTerm term) {
        return this.lessThanEquals(this.getTermFactory().zero(), term);
    }

    /**
     * @param term Some term.
     * @return The relation "term <= 0".
     */
    public LLVMRelation nonPositive(LLVMTerm term) {
        return this.lessThanEquals(term, this.getTermFactory().zero());
    }

    /**
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @return The relation lhs != rhs.
     */
    public LLVMRelation notEqualTo(LLVMTerm lhs, LLVMTerm rhs) {
        return this.createRelation(IntegerRelationType.NE, lhs, rhs);
    }

    /**
     * @param term Some term.
     * @return The relation "1 <= term".
     */
    public LLVMRelation positive(LLVMTerm term) {
        return this.lessThanEquals(this.getTermFactory().one(), term);
    }

}
