package aprove.input.Programs.llvm.internalStructures.module;

import java.math.BigInteger;

import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Janine Repke, CryingShadow
 * Gathers the types of binary operations.
 */
public enum LLVMBinaryOpType {

    /**
     * Integer addition.
     */
    ADD {
        
        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            if (!(state instanceof LLVMHeuristicState) || !(t1 instanceof LLVMHeuristicVariable)
                || !(t2 instanceof LLVMHeuristicVariable)) {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
            }
            final AbstractBoundedInt val1 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t1).getThisAsAbstractBoundedInt();
            final AbstractBoundedInt val2 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t2).getThisAsAbstractBoundedInt();
            BigInteger newLower = val1.getLower().getConstant().add(val2.getLower().getConstant());
            BigInteger newUpper = val1.getUpper().getConstant().add(val2.getUpper().getConstant());
            if (newUpper.compareTo(type.getUpper().getConstant()) <= 0) return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
            if (newLower.compareTo(type.getUpper().getConstant()) > 0) return new Pair<YNM,YNM>(YNM.YES, YNM.YES);
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
        }
        
        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            if (!(state instanceof LLVMHeuristicState) || !(t1 instanceof LLVMHeuristicVariable)
                || !(t2 instanceof LLVMHeuristicVariable)) {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
            }
            final AbstractBoundedInt val1 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t1).getThisAsAbstractBoundedInt();
            final AbstractBoundedInt val2 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t2).getThisAsAbstractBoundedInt();
            BigInteger newLower = val1.getLower().getConstant().add(val2.getLower().getConstant());
            BigInteger newUpper = val1.getUpper().getConstant().add(val2.getUpper().getConstant());
            if (newLower.compareTo(type.getLower().getConstant()) >= 0) return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
            if (newUpper.compareTo(type.getLower().getConstant()) < 0) return new Pair<YNM,YNM>(YNM.YES, YNM.YES);
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            return
                new Pair<LLVMTerm, LLVMAbstractState>(state.getRelationFactory().getTermFactory().add(lhs, rhs), state);
        }

        @Override
        public boolean isOverapproximation() {
            return false;
        }
    },

    /**
     * Logical AND.
     */
    AND {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            return
                new Pair<LLVMTerm, LLVMAbstractState>(
                    state.getRelationFactory().getTermFactory().and(lhs, rhs),
                    state
                );
        }

        @Override
        public boolean isOverapproximation() {
            return false;
        }
    },

    /**
     * Arithmetic right-shift (with sign extension). Exposes undefined behavior if the second operand is too large. The
     * second operand is treated as an unsigned value. If the exact keyword is present, the result is a trap value if
     * non-zero bits are shifted out.
     */
    ASHR {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            // TODO implement me
            throw new UnsupportedOperationException("Not yet implemented!");
        }

        @Override
        public boolean isOverapproximation() {
            throw new UnsupportedOperationException("Not yet implemented!");
        }
    },

    /**
     * Floating point addition.
     */
    FADD {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            // TODO we return just a fresh variable as we cannot correctly handle floating point arithmetic yet
            return
                new Pair<LLVMTerm, LLVMAbstractState>(
                    state.getRelationFactory().getTermFactory().freshVariable(),
                    state
                );
        }

        @Override
        public boolean isOverapproximation() {
            return true;
        }
    },

    /**
     * Floating point division.
     */
    FDIV {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            // TODO we return just a fresh variable as we cannot correctly handle floating point arithmetic yet
            return
                new Pair<LLVMTerm, LLVMAbstractState>(
                    state.getRelationFactory().getTermFactory().freshVariable(),
                    state
                );
        }

        @Override
        public boolean isOverapproximation() {
            return true;
        }
    },

    /**
     * Floating point multiplication.
     */
    FMUL {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            // TODO we return just a fresh variable as we cannot correctly handle floating point arithmetic yet
            return
                new Pair<LLVMTerm, LLVMAbstractState>(
                    state.getRelationFactory().getTermFactory().freshVariable(),
                    state
                );
        }

        @Override
        public boolean isOverapproximation() {
            return true;
        }
    },

    /**
     * Floating point modulo.
     */
    FREM {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            // TODO we return just a fresh variable as we cannot correctly handle floating point arithmetic yet
            return
                new Pair<LLVMTerm, LLVMAbstractState>(
                    state.getRelationFactory().getTermFactory().freshVariable(),
                    state
                );
        }

        @Override
        public boolean isOverapproximation() {
            return true;
        }
    },

    /**
     * Floating point subtraction.
     */
    FSUB {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            // TODO we return just a fresh variable as we cannot correctly handle floating point arithmetic yet
            return
                new Pair<LLVMTerm, LLVMAbstractState>(
                    state.getRelationFactory().getTermFactory().freshVariable(),
                    state
                );
        }

        @Override
        public boolean isOverapproximation() {
            return true;
        }
    },

    /**
     * Logical right-shift (with zero extension). Exposes undefined behavior if the second operand is too large. The
     * second operand is treated as an unsigned value. If the exact keyword is present, the result is a trap value if
     * non-zero bits are shifted out.
     */
    LSHR {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            // TODO we return just a fresh variable as we cannot correctly handle shifts yet
            return
                new Pair<LLVMTerm, LLVMAbstractState>(
                    state.getRelationFactory().getTermFactory().freshVariable(),
                    state
                );
        }

        @Override
        public boolean isOverapproximation() {
            throw new UnsupportedOperationException("Not yet implemented!");
        }
    },

    /**
     * Integer multiplication.
     */
    MUL {
        
        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            if (!(state instanceof LLVMHeuristicState) || !(t1 instanceof LLVMHeuristicVariable)
                || !(t2 instanceof LLVMHeuristicVariable)) {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
            }
            final AbstractBoundedInt val1 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t1).getThisAsAbstractBoundedInt();
            final AbstractBoundedInt val2 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t2).getThisAsAbstractBoundedInt();
            //[a,b] * [c,d] = [min{ac,ad,bc,bd}, max{ac,ad,bc,bd}]
            final IntervalBound ac = val1.getLower().mul(val2.getLower());
            final IntervalBound ad = val1.getLower().mul(val2.getUpper());
            final IntervalBound bc = val1.getUpper().mul(val2.getLower());
            final IntervalBound bd = val1.getUpper().mul(val2.getUpper());
            final BigInteger newLower = ac.min(ad).min(bc).min(bd).getConstant();
            final BigInteger newUpper = ac.max(ad).max(bc).max(bd).getConstant();
            if (newUpper.compareTo(type.getUpper().getConstant()) <= 0) return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
            BigInteger size = type.getUpper().getConstant().subtract(type.getLower().getConstant()).add(BigInteger.ONE);
            if (newLower.compareTo(type.getUpper().getConstant()) > 0) {
                if (newUpper.compareTo(type.getUpper().getConstant().add(size)) > 0) {
                    return new Pair<YNM,YNM>(YNM.YES, YNM.NO);
                } else {
                    return new Pair<YNM,YNM>(YNM.YES, YNM.YES);
                }
            }
            if (newUpper.compareTo(type.getUpper().getConstant().add(size)) > 0) {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.NO);
            } else {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
            }
        }
        
        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            if (!(state instanceof LLVMHeuristicState) || !(t1 instanceof LLVMHeuristicVariable)
                || !(t2 instanceof LLVMHeuristicVariable)) {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
            }
            final AbstractBoundedInt val1 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t1).getThisAsAbstractBoundedInt();
            final AbstractBoundedInt val2 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t2).getThisAsAbstractBoundedInt();
            //[a,b] * [c,d] = [min{ac,ad,bc,bd}, max{ac,ad,bc,bd}]
            final IntervalBound ac = val1.getLower().mul(val2.getLower());
            final IntervalBound ad = val1.getLower().mul(val2.getUpper());
            final IntervalBound bc = val1.getUpper().mul(val2.getLower());
            final IntervalBound bd = val1.getUpper().mul(val2.getUpper());
            final BigInteger newLower = ac.min(ad).min(bc).min(bd).getConstant();
            final BigInteger newUpper = ac.max(ad).max(bc).max(bd).getConstant();
            if (newLower.compareTo(type.getLower().getConstant()) >= 0) return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
            BigInteger size = type.getUpper().getConstant().subtract(type.getLower().getConstant()).add(BigInteger.ONE);
            if (newUpper.compareTo(type.getLower().getConstant()) < 0) {
                if (newLower.compareTo(type.getLower().getConstant().subtract(size)) < 0) {
                    return new Pair<YNM,YNM>(YNM.YES, YNM.NO);
                } else {
                    return new Pair<YNM,YNM>(YNM.YES, YNM.YES);
                }
            }
            if (newLower.compareTo(type.getLower().getConstant().subtract(size)) < 0) {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.NO);
            } else {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
            }
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            return
                new Pair<LLVMTerm, LLVMAbstractState>(
                    state.getRelationFactory().getTermFactory().mult(lhs, rhs),
                    state
                );
        }

        @Override
        public boolean isOverapproximation() {
            return false;
        }
    },

    /**
     * Logical OR.
     */
    OR {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            return
                new Pair<LLVMTerm, LLVMAbstractState>(
                    state.getRelationFactory().getTermFactory().operation(ArithmeticOperationType.OR, lhs, rhs),
                    state
                );
        }

        @Override
        public boolean isOverapproximation() {
            return false;
        }
    },

    /**
     * Signed truncating integer division.
     */
    SDIV {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            if (!(state instanceof LLVMHeuristicState) || !(t1 instanceof LLVMHeuristicVariable)
                || !(t2 instanceof LLVMHeuristicVariable)) {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
            }
            final AbstractBoundedInt val1 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t1).getThisAsAbstractBoundedInt();
            final AbstractBoundedInt val2 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t2).getThisAsAbstractBoundedInt();
            // MININT / -1 leads to an overflow
            if (!val1.containsLiteral(type.getLower().getConstant()) || !val2.containsLiteral(-1)) {
                return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
            }
            if (val1.getLower().isNegative()
                    && val1.getLower().equals(val1.getUpper()) && val1.getLower().equals(type.getLower())
                    && val2.getLower().equals(val2.getUpper()) && val2.getLower().equals(IntervalBound.NEGONE)) {
                return new Pair<YNM,YNM>(YNM.YES, YNM.YES);
            }
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            final LLVMRelationFactory relationFactory = state.getRelationFactory();
            final LLVMTermFactory termFactory = relationFactory.getTermFactory();
            final Pair<Boolean, ? extends LLVMAbstractState> check =
                state.checkRelation(relationFactory.notEqualTo(rhs, termFactory.zero()), aborter);
            if (check.x) {
                return new Pair<LLVMTerm, LLVMAbstractState>(termFactory.tidiv(lhs, rhs), check.y);
            }
            throw new UndefinedBehaviorException("Division by zero possible at node " + nodeNumber);
        }

        @Override
        public boolean isOverapproximation() {
            return false;
        }
    },

    /**
     * Left-shift. Exposes undefined behavior if the second operand is too large. The second operand is treated as an
     * unsigned value. If the nuw or nsw keywords are present, the result is a trap value if non-zero or non-sign bits
     * are shifted out, respectively.
     */
    SHL {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            // TODO Auto-generated method stub
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.MAYBE);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            // TODO implement me
            throw new UnsupportedOperationException("Not yet implemented!");
        }

        @Override
        public boolean isOverapproximation() {
            throw new UnsupportedOperationException("Not yet implemented!");
        }
    },

    /**
     * Signed integer remainder (not modulo - the result has the same sign as the dividend/first operand).
     */
    SREM {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            if (!(state instanceof LLVMHeuristicState) || !(t1 instanceof LLVMHeuristicVariable)
                || !(t2 instanceof LLVMHeuristicVariable)) {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
            }
            final AbstractBoundedInt val1 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t1).getThisAsAbstractBoundedInt();
            final AbstractBoundedInt val2 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t2).getThisAsAbstractBoundedInt();
            // MININT SREM -1 leads to an overflow
            if (!val1.containsLiteral(type.getLower().getConstant()) || !val2.containsLiteral(-1)) {
                return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
            }
            if (val1.getLower().isNegative()
                    && val1.getLower().equals(val1.getUpper()) && val1.getLower().equals(type.getLower())
                    && val2.getLower().equals(val2.getUpper()) && val2.getLower().equals(IntervalBound.NEGONE)) {
                return new Pair<YNM,YNM>(YNM.YES, YNM.YES);
            }
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            final LLVMRelationFactory relationFactory = state.getRelationFactory();
            final LLVMTermFactory termFactory = relationFactory.getTermFactory();
            final Pair<Boolean, ? extends LLVMAbstractState> check =
                state.checkRelation(relationFactory.notEqualTo(rhs, termFactory.zero()), aborter);
            if (check.x) {
                return
                    new Pair<LLVMTerm, LLVMAbstractState>(
                        termFactory.operation(ArithmeticOperationType.TMOD, lhs, rhs),
                        check.y
                    );
            }
            throw new UndefinedBehaviorException("Division by zero possible at node " + nodeNumber);
        }

        @Override
        public boolean isOverapproximation() {
            return false;
        }
    },

    /**
     * Integer subtraction.
     */
    SUB {
        
        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            if (!(state instanceof LLVMHeuristicState) || !(t1 instanceof LLVMHeuristicVariable)
                || !(t2 instanceof LLVMHeuristicVariable)) {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
            }
            final AbstractBoundedInt val1 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t1).getThisAsAbstractBoundedInt();
            final AbstractBoundedInt val2 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t2).getThisAsAbstractBoundedInt();
            BigInteger newLower = val1.getLower().getConstant().subtract(val2.getUpper().getConstant());
            BigInteger newUpper = val1.getUpper().getConstant().subtract(val2.getLower().getConstant());
            if (newUpper.compareTo(type.getUpper().getConstant()) <= 0) return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
            if (newLower.compareTo(type.getUpper().getConstant()) > 0) return new Pair<YNM,YNM>(YNM.YES, YNM.YES);
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
        }
        
        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            if (!(state instanceof LLVMHeuristicState) || !(t1 instanceof LLVMHeuristicVariable)
                || !(t2 instanceof LLVMHeuristicVariable)) {
                return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
            }
            final AbstractBoundedInt val1 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t1).getThisAsAbstractBoundedInt();
            final AbstractBoundedInt val2 =
                ((LLVMHeuristicState)state).getValue((LLVMHeuristicVariable)t2).getThisAsAbstractBoundedInt();
            BigInteger newLower = val1.getLower().getConstant().subtract(val2.getUpper().getConstant());
            BigInteger newUpper = val1.getUpper().getConstant().subtract(val2.getLower().getConstant());
            if (newLower.compareTo(type.getLower().getConstant()) >= 0) return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
            if (newUpper.compareTo(type.getLower().getConstant()) < 0) return new Pair<YNM,YNM>(YNM.YES, YNM.YES);
            return new Pair<YNM,YNM>(YNM.MAYBE, YNM.YES);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            return
                new Pair<LLVMTerm, LLVMAbstractState>(state.getRelationFactory().getTermFactory().sub(lhs, rhs), state);
        }

        @Override
        public boolean isOverapproximation() {
            return false;
        }
    },

    /**
     * Unsigned integer division.
     */
    UDIV {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            final LLVMRelationFactory relationFactory = state.getRelationFactory();
            final LLVMTermFactory termFactory = relationFactory.getTermFactory();
            final Pair<Boolean, ? extends LLVMAbstractState> check =
                state.checkRelation(relationFactory.notEqualTo(rhs, termFactory.zero()), aborter);
            if (check.x) {
                return new Pair<LLVMTerm, LLVMAbstractState>(termFactory.tidiv(lhs, rhs), check.y);
            }
            throw new UndefinedBehaviorException("Division by zero possible at node " + nodeNumber);
        }

        @Override
        public boolean isOverapproximation() {
            return false;
        }
    },

    /**
     * Unsigned integer remainder (in the unsigned case, remainder and modulo are identical).
     */
    UREM {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            final LLVMRelationFactory relationFactory = state.getRelationFactory();
            final LLVMTermFactory termFactory = relationFactory.getTermFactory();
            final Pair<Boolean, ? extends LLVMAbstractState> check =
                state.checkRelation(relationFactory.notEqualTo(rhs, termFactory.zero()), aborter);
            if (check.x) {
                return
                    new Pair<LLVMTerm, LLVMAbstractState>(
                        termFactory.operation(ArithmeticOperationType.TMOD, lhs, rhs),
                        check.y
                    );
            }
            throw new UndefinedBehaviorException("Division by zero possible at node " + nodeNumber);
        }

        @Override
        public boolean isOverapproximation() {
            return false;
        }
    },

    /**
     * Logical XOR.
     */
    XOR {

        @Override
        public Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2) {
            return new Pair<YNM,YNM>(YNM.NO, YNM.NO);
        }

        @Override
        public Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
            LLVMAbstractState state,
            LLVMTerm lhs,
            LLVMTerm rhs,
            int nodeNumber,
            Abortion aborter
        ) throws UndefinedBehaviorException {
            LLVMBinaryOpType.checkTrap(state, lhs, rhs, nodeNumber);
            // TODO we return just a fresh variable as we cannot correctly handle floating point arithmetic yet
            return
                new Pair<LLVMTerm, LLVMAbstractState>(
                    state.getRelationFactory().getTermFactory().operation(ArithmeticOperationType.XOR, lhs, rhs),
                    state
                );
        }

        @Override
        public boolean isOverapproximation() {
            return false;
        }
    };
    
    /**
     * @param state The current state.
     * @param type The integer type of the result.
     * @param t1 The first term.
     * @param t2 The second term.
     * @return First value: Does an overflow occur? Second value: Is it a simple overflow?
     */
    public abstract Pair<YNM,YNM> checkBoundsForOverflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2);
    
    /**
     * @param state The current state.
     * @param type The integer type of the result.
     * @param t1 The first term.
     * @param t2 The second term.
     * @return First value: Does an underflow occur? Second value: Is it a simple underflow?
     */
    public abstract Pair<YNM,YNM> checkBoundsForUnderflow(LLVMAbstractState state, IntegerType type, LLVMTerm t1, LLVMTerm t2);

    /**
     * @param state The current state.
     * @param lhs The left-hand side of an operation.
     * @param rhs The right-hand side of an operation.
     * @param nodeNumber The current node number.
     * @throws UndefinedBehaviorException If either side is a possible trap value.
     */
    private static void checkTrap(LLVMAbstractState state, LLVMTerm lhs, LLVMTerm rhs, int nodeNumber)
    throws UndefinedBehaviorException {
        if (
            lhs instanceof LLVMSymbolicVariable && state.isPossiblyTrapValue((LLVMSymbolicVariable)lhs)
            || rhs instanceof LLVMSymbolicVariable && state.isPossiblyTrapValue((LLVMSymbolicVariable)rhs)
        ) {
            throw new UndefinedBehaviorException("Accessing possible trap value at node " + nodeNumber + ".");
        }
    }

    /**
     * @param state The abstract state holding the relevant knowledge.
     * @param lhs The left-hand side.
     * @param rhs The right-hand side.
     * @param nodeNumber The current node number.
     * @return An LLVM term representing this operation applied to the specified arguments and the specified LLVM state
     *         possibly updated during checks.
     * @throws UndefinedBehaviorException If this operation might expose undefined behavior.
     */
    public abstract Pair<LLVMTerm, LLVMAbstractState> toLLVMTerm(
        LLVMAbstractState state,
        LLVMTerm lhs,
        LLVMTerm rhs,
        int nodeNumber,
        Abortion aborter
    ) throws UndefinedBehaviorException;

    @Override
    public String toString() {
        return this.name().toLowerCase();
    }

    /**
     * Whether or not the evaluation of this operator over-approximates its actual result. Returning 
     * <code>true</code> does not imply over-approximation but <code>false</code> guarantees that 
     * the result is accurate 
     * @return <code>false</code> if the evaluation result is guaranteed to be no over-approximation
     */
    public abstract boolean isOverapproximation();
}
