/**
 * @author Marc Brockschmidt
 */

package aprove.verification.oldframework.Bytecode.OpCodes;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of IF*, GOTO and JSR* opcodes.
 */
public class Branch extends OpCode {
    /**
     * Enumeration of possible condition types.
     */
    public enum ComparisonType {
        /**
         * Equality check
         */
        EQ,

        /**
         * Inequality check
         */
        NE,

        /**
         * Arithmetic littler
         */
        LT,

        /**
         * Arithmetic greater or equality
         */
        GE,

        /**
         * Arithmetic greater
         */
        GT,

        /**
         * Arithmetic littler or equality
         */
        LE,

        /**
         * Equality with the NULL pointer
         */
        NULL,

        /**
         * Inequality with the NULL pointer
         */
        NONNULL,

        /**
         * Unconditional branching (goto/jump)
         */
        JMP;

        /**
         * Invert the {@link ComparisonType}
         * @return the inverted comparison enum constant
         */
        public final ComparisonType invert() {
            switch (this) {
            case EQ:
                return NE;
            case NE:
                return EQ;
            case LT:
                return GE;
            case LE:
                return GT;
            case GT:
                return LE;
            case GE:
                return LT;
            case NULL:
                return NONNULL;
            case NONNULL:
                return NULL;
            default:
                assert (false);
                return null;
            }
        }

        /**
         * @return the mirror of this relation. For the original relation R and
         * the mirror R': xRy <=> yR'x
         */
        public ComparisonType mirror() {
            switch (this) {
            case EQ:
                return EQ;
            case NE:
                return NE;
            case LT:
                return GT;
            case LE:
                return GE;
            case GT:
                return LT;
            case GE:
                return LE;
            default:
                assert false;
                return null;
            }
        }

        /**
         * @return the respective integer relation type, or NULL if
         * not applicable.
         */
        public IntegerRelationType toIntegerRelationType() {
            switch (this) {
            case EQ:
                return IntegerRelationType.EQ;
            case NE:
                return IntegerRelationType.NE;
            case LT:
                return IntegerRelationType.LT;
            case LE:
                return IntegerRelationType.LE;
            case GT:
                return IntegerRelationType.GT;
            case GE:
                return IntegerRelationType.GE;
            default:
                assert false;
                return null;
            }
        }
    }

    /**
     * The type of the comparison used in the branch condition.
     */
    private final ComparisonType compT;

    /**
     * The type of the arguments of the branch condition.
     */
    private final OperandType argumentT;

    /**
     * True iff two arguments are compared. False iff only one argument a is
     * compared to 0, that is, a COND 0
     */
    private final boolean comp2Args;

    /**
     * Offset of the branch target relative to this opcode.
     */
    private final int branchOffset;

    /**
     * Actual opcode at this opcode + offset.
     */
    private OpCode branchTarget;

    /**
     * Marks if this is a subroutine jump. If so, the following opcode address
     * needs to be pushed onto the stack, to return from the subroutine.
     */
    private final boolean isSubroutine;

    /**
     * Constructs a new Branch object, representing an instance of one of IF*
     * opcodes or a GOTO.
     * @param offset offset in bytes of the branch target
     * @param comparesTwoArguments true iff two stack values are compared, false
     * iff only the topmost is compared against 0
     * @param comparisonType type of comparison (usually one of >=, >, =, ...)
     * @param argumentType type of the compared values
     * @param isSR true iff this branches into a subroutine
     */
    public Branch(
        final int offset,
        final boolean comparesTwoArguments,
        final ComparisonType comparisonType,
        final OperandType argumentType,
        final boolean isSR)
    {
        this.branchOffset = offset;
        this.comp2Args = comparesTwoArguments;
        this.compT = comparisonType;
        this.argumentT = argumentType;
        this.isSubroutine = isSR;
    }

    /**
     * Returns the offset in number of bytes of the branch target of this
     * instance.
     * @return offset of branch target (as number of bytes)
     */
    public final int getBranchOffset() {
        return this.branchOffset;
    }

    /**
     * Sets the branch target to an already existing OpCode object.
     * @param branchTargetOpCode the target opcode
     */
    public final void setBranchTarget(final OpCode branchTargetOpCode) {
        assert (branchTargetOpCode != null);
        this.branchTarget = branchTargetOpCode;
    }

    /**
     * Returns the opcode that is the target of this branch instance.
     * @return target OpCode
     */
    public final OpCode getBranchTarget() {
        return this.branchTarget;
    }

    /**
     * @return String representation of this branch opcode
     */
    @Override
    public final String toString() {
        if (this.isSubroutine) {
            return "jsr";
        } else if (this.compT == ComparisonType.JMP) {
            return "jmp";
        } else if (this.comp2Args) {
            return this.compT.toString();
        } else {
            if (this.argumentT == OperandType.ADDRESS) {
                return "IF_" + this.compT.toString();
            }
            return this.compT + " 0";
        }
    }

    /**
     * @return the type of comparison used in this branch instance
     */
    public final ComparisonType getCompT() {
        return this.compT;
    }

    /**
     * Evaluate the condition
     * @return the resulting states and edges
     * @param state the original state
     */
    @Override
    public final Pair<State, EvaluationEdge> evaluate(final State state) {
        /*
         * General flow idea:
         *  Determine ComparisionType, have one function handling each group
         *  - JMP: Heh, easy
         *  - Subroutine: Create a ReturnAddress and put it onto the operand stack
         *  - Everything else:
         *    Check operand type, have one method for
         *     o Integer
         *     o Floats [1]
         *     o Addresses
         */
        /*
         * Comment FKuerten:
         * [1] None of the OpCodes handled here allow floats as parameters.
         * In fact, float comparision is done using FCMP* which pushes -1,0 or 1
         * on the operand stack which then can be checked using IF*.
         * See Cmp.
         * So we don't have to support floats (or doubles) here.
         */

        if (this.compT == ComparisonType.JMP) {
            final State newState = state.clone();
            final StackFrame sf = newState.getCurrentStackFrame();
            sf.setCurrentOpCode(this.getBranchTarget());
            if (this.isSubroutine) {
                final ReturnAddress ra = new ReturnAddress(this.getNextOp());
                sf.getOperandStack().push(ra);
            }
            return new Pair<>(newState, new EvaluationEdge());
        }
        switch (this.argumentT) {
        case INTEGER:
            final IntegerRelationType intRel = this.compT.toIntegerRelationType();
            return this.intEvaluate(intRel, state);
        case ADDRESS:
            return this.addrEvaluate(state);
        default:
            assert (false) : "We can't handle anything but integers and addresses for now";
        }
        assert (false);
        return null;
    }

    /**
     * Find out if we need to refine. If so, do it :)
     * @param s the original state
     * @param out the resulting refined states and edges (if any)
     * @return true if refinement was needed (and done)
     */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        if (this.compT == ComparisonType.JMP) {
            return false;
        }

        switch (this.argumentT) {
        case INTEGER:
            return this.intRefine(s, out);
        case ADDRESS:
            return this.addrRefine(s, out);
        default:
            assert (false) : "We can't handle anything but integers and addresses for now";
        }

        assert (false) : "Shouldn't reach this.";
        return false;
    }

    /**
     * When refinement failed, simply creating two successors where the result
     * (TRUE or FALSE) is hard-wired is our only option. This function
     * implements this behavior.
     *
     * @param curState the current state
     * @param y the value of the second argument
     * @param xR the reference to the first argument
     * @param yR the reference to the second argument
     * @param newStates the resulting states will be stored here
     */
    private void split(
        final State curState,
        final AbstractInt y,
        final AbstractVariableReference xR,
        final AbstractVariableReference yR,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates)
    {
        final State newStateTrue = curState.clone();
        final State newStateFalse = curState.clone();
        newStateTrue.setSplitResult(new BooleanSplitResult(true));
        newStateFalse.setSplitResult(new BooleanSplitResult(false));

        /*
         * For ==, != one of the cases implies the identity of the left and
         * right variable reference. We can reflect this when doing the split
         * by simply using the same variable reference on both sides of the
         * relation:
         */
        if (this.compT.equals(ComparisonType.EQ)) {
            AbstractVariableReference newyRef = yR;
            /*
             * If this branch opcode had only one argument, yR is empty, thus
             * we need to create a reference to the constant first:
             */
            if (yR == null) {
                newyRef = newStateTrue.createReferenceAndAdd(y, this.argumentT);
            }
            newStateTrue.replaceReference(xR, newyRef);
        }
        if (this.compT.equals(ComparisonType.NE)) {
            AbstractVariableReference newyRef = yR;
            /*
             * If this branch opcode had only one argument, yR is empty, thus
             * we need to create a reference to the constant first:
             */
            if (yR == null) {
                newyRef = newStateFalse.createReferenceAndAdd(y, this.argumentT);
            }
            newStateFalse.replaceReference(xR, newyRef);
        }

        final LinkedHashSet<AbstractVariableReference> refs = new LinkedHashSet<>();
        refs.add(xR);
        refs.add(yR);

        IntegerRelationType intRel = this.compT.toIntegerRelationType();

        if (!curState.checkIntegerRelation(xR, intRel.invert(), yR)) {
            final SplitEdge edgeTrue = new SplitEdge(refs);
            edgeTrue.add(new JBCIntegerRelation(xR, intRel, yR));
            newStateTrue.getIntegerRelations().note(xR, intRel, yR);
            newStates.add(new Pair<State, EdgeInformation>(newStateTrue, edgeTrue));
        }

        if (!curState.checkIntegerRelation(xR, intRel, yR)) {
            final SplitEdge edgeFalse = new SplitEdge(refs);
            edgeFalse.add(new JBCIntegerRelation(xR, intRel.invert(), yR));
            newStateFalse.getIntegerRelations().note(xR, intRel.invert(), yR);
            newStates.add(new Pair<State, EdgeInformation>(newStateFalse, edgeFalse));
        }
    }

    /**
     * Try to decide the condition.
     * @param intRel the integer relation
     * @param curState the current state
     * @return next state
     */
    private Pair<State, EvaluationEdge> intEvaluate(final IntegerRelationType intRel, final State curState) {
        /*
         * Get the values we want to work on.
         */
        AbstractInt x;
        AbstractVariableReference xR;
        AbstractInt y;
        AbstractVariableReference yR;
        final StackFrame curFrame = curState.getCurrentStackFrame();

        if (this.comp2Args) {
            yR = curFrame.peekOperandStack(0);
            xR = curFrame.peekOperandStack(1);
            assert (curState.getAbstractVariable(xR) instanceof AbstractInt && curState.getAbstractVariable(yR) instanceof AbstractInt);
            y = (AbstractInt) curState.getAbstractVariable(yR);
            x = (AbstractInt) curState.getAbstractVariable(xR);
        } else {
            yR = null;
            xR = curFrame.peekOperandStack(0);
            assert (curState.getAbstractVariable(xR) instanceof AbstractInt);
            x = (AbstractInt) curState.getAbstractVariable(xR);
            y = AbstractInt.getZero();
        }

        final SplitResult splitRes = curState.getSplitResult();
        Boolean result = null;
        if (splitRes != null) {
            result = ((BooleanSplitResult) splitRes).getTruthValue();
        }

        /* Check if this comparison is evaluated to true: */
        final boolean sameRef = xR.equals(yR);

        final boolean areUnequal;
        if (yR != null) {
            areUnequal = curState.checkIntegerRelation(xR, IntegerRelationType.NE, yR);
        } else {
            areUnequal = false;
        }
        IntegerRelationType intRelInv = intRel.invert();
        if (yR != null) {
            if (result == null && curState.checkIntegerRelation(xR, intRel, yR)) {
                result = Boolean.TRUE;
            }
            if (result == null && curState.checkIntegerRelation(xR, intRelInv, yR)) {
                result = Boolean.FALSE;
            }
        }
        if (result == null && AbstractInt.computeComparisonResult(intRel, x, y, sameRef, areUnequal)) {
            result = Boolean.TRUE;
        }
        if (result == null && AbstractInt.computeComparisonResult(intRelInv, x, y, sameRef, areUnequal)) {
            result = Boolean.FALSE;
        }
        if (result != null) {
            final State newState = curState.clone();
            //Get rid of the (used up) arguments:
            newState.getCurrentStackFrame().popOperandStack();
            if (this.comp2Args) {
                newState.getCurrentStackFrame().popOperandStack();
            }
            final EvaluationEdge edge = new EvaluationEdge();
            IntegerRelationType trueRel;
            if (result.booleanValue()) {
                trueRel = intRel;
                newState.getCurrentStackFrame().setCurrentOpCode(this.getBranchTarget());
            } else {
                trueRel = intRel.invert();
                newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());
            }

            if (trueRel == IntegerRelationType.GE
                && yR != null
                && curState.getIntegerRelations().contains(new JBCIntegerRelation(xR, IntegerRelationType.NE, yR)))
            {
                trueRel = IntegerRelationType.GT;
            } else if (trueRel == IntegerRelationType.LE
                && yR != null
                && curState.getIntegerRelations().contains(new JBCIntegerRelation(xR, IntegerRelationType.NE, yR)))
            {
                trueRel = IntegerRelationType.LT;
            }

            //Some optimizations: If we decided that xR >= yR, then a lower bound for yR is also a lower bound for xR
            if (splitRes != null) {
                // x < y => x != MAXINT
                if (trueRel == IntegerRelationType.LT && x.getUpper().isFinite()) {
                    final BigInteger max = xR.getPrimitiveType().getMaxValue();
                    final BigInteger constant = x.getUpper().getConstant();
                    if (max.equals(constant)) {
                        final IntervalBound newUpper = x.getUpper().add(IntervalBound.NEGONE);
                        x =
                            AbstractInt.create(
                                x.getLower(),
                                newUpper,
                                x.getMinLower(),
                                x.getMaxUpper(),
                                x.getLowerCounter(),
                                x.getUpperCounter());
                        newState.removeAbstractVariable(xR);
                        newState.addAbstractVariable(xR, x);
                    }
                }

                // x > y => y != MAXINT
                if (yR != null && trueRel == IntegerRelationType.GT && y.getUpper().isFinite()) {
                    final BigInteger max = yR.getPrimitiveType().getMaxValue();
                    final BigInteger constant = y.getUpper().getConstant();
                    if (max.equals(constant)) {
                        final IntervalBound newUpper = y.getUpper().add(IntervalBound.NEGONE);
                        y =
                            AbstractInt.create(
                                y.getLower(),
                                newUpper,
                                y.getMinLower(),
                                y.getMaxUpper(),
                                y.getLowerCounter(),
                                y.getUpperCounter());
                        newState.removeAbstractVariable(yR);
                        newState.addAbstractVariable(yR, y);
                    }
                }

                // [xl,xu] <= [yl,yu] && xl > yl => Bullshit. So change y:
                if (trueRel == IntegerRelationType.LE
                    && (x.getLower().isFinite() || y.getLower().isFinite())
                    && x.getLower().compareTo(y.getLower()) > 0)
                {
                    y =
                        AbstractInt.create(
                            x.getLower(),
                            y.getUpper(),
                            y.getMinLower(),
                            y.getMaxUpper(),
                            y.getLowerCounter(),
                            y.getUpperCounter());
                    newState.removeAbstractVariable(yR);
                    newState.addAbstractVariable(yR, y);
                }

                // [xl, xu] < [yl, yu] && xl >= yl => Bullshit. So change yl to xl + 1:
                if (trueRel == IntegerRelationType.LT
                    && (x.getLower().isFinite() || y.getLower().isFinite())
                    && x.getLower().compareTo(y.getLower()) >= 0)
                {
                    y =
                        AbstractInt.create(
                            IntervalBound.create(x.getLower().getConstant().add(BigInteger.ONE)),
                            y.getUpper(),
                            y.getMinLower(),
                            y.getMaxUpper(),
                            y.getLowerCounter(),
                            y.getUpperCounter());
                    newState.removeAbstractVariable(yR);
                    newState.addAbstractVariable(yR, y);
                }

                // [xl,xu] >= [yl,yu] && xl < yl => Bullshit. So change x:
                if (trueRel == IntegerRelationType.GE
                    && (y.getLower().isFinite() || x.getLower().isFinite())
                    && y.getLower().compareTo(x.getLower()) > 0)
                {
                    x =
                        AbstractInt.create(
                            y.getLower(),
                            x.getUpper(),
                            x.getMinLower(),
                            x.getMaxUpper(),
                            x.getLowerCounter(),
                            x.getUpperCounter());
                    newState.removeAbstractVariable(xR);
                    newState.addAbstractVariable(xR, x);
                }

                // [xl, xu] > [yl, yu] && xl <= yl => Bullshit. So change xl to yl + 1:
                if (trueRel == IntegerRelationType.GT
                    && (y.getLower().isFinite() || x.getLower().isFinite())
                    && y.getLower().compareTo(x.getLower()) >= 0)
                {
                    x =
                        AbstractInt.create(
                            IntervalBound.create(y.getLower().getConstant().add(BigInteger.ONE)),
                            x.getUpper(),
                            x.getMinLower(),
                            x.getMaxUpper(),
                            x.getLowerCounter(),
                            x.getUpperCounter());
                    newState.removeAbstractVariable(xR);
                    newState.addAbstractVariable(xR, x);
                }

                //TODO This should be done for other cases, too (or we should think hard about it and find a more general way)
            }

            boolean contradictory = false;
            //If we have a NE, try to extract more specific information:
            if (trueRel == IntegerRelationType.NE && yR != null) {
                final boolean isLT =
                    AbstractInt.computeComparisonResult(IntegerRelationType.LT, x, y, sameRef, areUnequal);
                final boolean isGT;
                if (isLT) {
                    isGT = false;
                    trueRel = IntegerRelationType.LT;
                    contradictory |= newState.note(xR, trueRel, yR);
                } else {
                    isGT = AbstractInt.computeComparisonResult(IntegerRelationType.GT, x, y, sameRef, areUnequal);
                    if (isGT) {
                        trueRel = IntegerRelationType.GT;
                        contradictory |= newState.note(xR, trueRel, yR);
                    }
                }

                if (!isLT && !isGT) {
                    final IntegerRelations oldIntRels = curState.getIntegerRelations();

                    //(xR <= yR || yR >= xR) && xR != yR  --->  xR < yR
                    if (oldIntRels.contains(new JBCIntegerRelation(xR, IntegerRelationType.LE, yR))) {
                        trueRel = IntegerRelationType.LT;
                        contradictory |= newState.note(xR, IntegerRelationType.LT, yR);
                    }

                    //(xR >= yR || yR <= xR) && xR != yR  --->  xR > yR
                    if (oldIntRels.contains(new JBCIntegerRelation(xR, IntegerRelationType.GE, yR))) {
                        trueRel = IntegerRelationType.GT;
                        contradictory |= newState.note(xR, IntegerRelationType.GT, yR);
                    }
                }
            }
            if (trueRel != IntegerRelationType.EQ && yR != null) {
                contradictory |= newState.note(xR, trueRel, yR);
            }

            if (x.isLiteral()) {
                y.noteComparisonWith(intRelInv.mirror(), ((LiteralInt) x).getLiteral());
            }
            if (y.isLiteral()) {
                x.noteComparisonWith(intRelInv, ((LiteralInt) y).getLiteral());
            }
            //Note comparisons with non-literals and/or constant that were never
            //explicitly on the stack:
            if (!x.isLiteral() || !y.isLiteral() || yR == null) {
                addEdgeInfo(curState, edge, xR, trueRel, yR, y);
            }
            if (contradictory) {
                System.err.println("OpCode Branch: Evaluating a contradictory state!");
                return null;
            }
            return new Pair<>(newState, edge);
        }
        assert (false);
        return null;
    }

    /**
     * For some comparison x R y add this information to the edge.
     * @param curState the enclosing state
     * @param edge the edge to fill with information
     * @param xR the variable reference for the left hand side of the comparison
     * @param trueRel the relation with x R y is true
     * @param yR the variable reference for the right hand side of the
     * comparison (may be null)
     * @param y the variable for the right hand side of the comparison
     */
    static void addEdgeInfo(
        final State curState,
        final EvaluationEdge edge,
        final AbstractVariableReference xR,
        final IntegerRelationType trueRel,
        final AbstractVariableReference yR,
        final AbstractInt y)
    {
        // Add information that the relation holds
        if (yR == null) {
            if (y instanceof LiteralInt) {
                final LiteralInt yLitInt = (LiteralInt) y;
                //Try to be smarter:
                if (trueRel == IntegerRelationType.NE) {
                    final AbstractInt xVal = (AbstractInt) curState.getAbstractVariable(xR);
                    final BigInteger yLit = yLitInt.getLiteral();
                    if (xVal.getLower().compareTo(yLit) >= 0) {
                        edge.add(new JBCIntegerRelation(xR, IntegerRelationType.GT, yLitInt));
                        return;
                    } else if (xVal.getUpper().compareTo(yLit) <= 0) {
                        edge.add(new JBCIntegerRelation(xR, IntegerRelationType.LT, yLitInt));
                        return;
                    }
                }
                edge.add(new JBCIntegerRelation(xR, trueRel, yLitInt));
            }
        } else {
            edge.add(new JBCIntegerRelation(xR, trueRel, yR));
        }
    }

    /**
     * If evaluation is not possible, this method creates more useful states by
     * splitting the abstract integers in a way that allows to decide, or, as
     * last resort, by simply generating successors for the true and false case.
     * @param curState The old state.
     * @param out List of result states containing refined information.
     * @return true if refinement was needed and done
     */
    private boolean intRefine(final State curState, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        /* Check if we have already decided this one: */
        if (curState.getSplitResult() != null) {
            return false;
        }

        /* Get the needed data: */
        AbstractInt x;
        AbstractVariableReference xR;
        AbstractInt y;
        AbstractVariableReference yR = null;
        final StackFrame curFrame = curState.getCurrentStackFrame();

        if (this.comp2Args) {
            yR = curFrame.peekOperandStack(0);
            xR = curFrame.peekOperandStack(1);
            assert (curState.getAbstractVariable(xR) instanceof AbstractInt && curState.getAbstractVariable(yR) instanceof AbstractInt);
            y = (AbstractInt) curState.getAbstractVariable(yR);
            x = (AbstractInt) curState.getAbstractVariable(xR);

        } else {
            xR = curFrame.peekOperandStack(0);
            assert (curState.getAbstractVariable(xR) instanceof AbstractInt);
            x = (AbstractInt) curState.getAbstractVariable(xR);
            y = AbstractInt.getZero();
        }

        final IntegerRelationType intRel = this.compT.toIntegerRelationType();

        /* Check if this comparison can be evaluated: */
        final boolean sameRef = xR.equals(yR);
        final boolean areUnequal;
        if (yR != null) {
            areUnequal = curState.checkIntegerRelation(xR, IntegerRelationType.NE, yR);
        } else {
            areUnequal = false;
        }
        if (AbstractInt.isDecidableComparison(intRel, x, y, sameRef, areUnequal)) {
            return false;
        }

        /* Try to refine: */
        final Collection<Pair<AbstractInt, AbstractInt>> resultVariables =
            IntegerRefinement.forIntegerRelation(x, y, this.compT.toIntegerRelationType());
        if (resultVariables != null) {
            for (final Pair<AbstractInt, AbstractInt> t : resultVariables) {
                final State newState = curState.clone();
                if (this.comp2Args) {
                    final AbstractVariableReference newXR = newState.createReferenceAndAdd(t.x, this.argumentT);
                    final AbstractVariableReference newYR = newState.createReferenceAndAdd(t.y, this.argumentT);
                    newState.replaceReference(xR, newXR);
                    newState.replaceReference(yR, newYR);
                    Map<AbstractVariableReference, AbstractInt> refinedInts = new LinkedHashMap<>();
                    refinedInts.put(newXR, t.x);
                    refinedInts.put(newYR, t.y);
                    Map<AbstractVariableReference, AbstractVariableReference> refRenaming = trimRelatedIntegers(refinedInts,
                            newState);
                    if (!newState.getIntegerRelations().isContradictory()) {
                        // construct the reference renaming; take into account that 'trimRelatedIntegers'
                        // might have renamed the references that were just refined
                        if (refRenaming.containsKey(newXR)) {
                            refRenaming.put(xR, refRenaming.get(newXR));
                            refRenaming.remove(newXR);
                        } else {
                            refRenaming.put(xR, newXR);
                        }
                        if (refRenaming.containsKey(newYR)) {
                            refRenaming.put(yR, refRenaming.get(newYR));
                            refRenaming.remove(newYR);
                        } else {
                            refRenaming.put(yR, newYR);
                        }
                        final RefinementEdge edge = new RefinementEdge("", refRenaming);
                        if (newXR.pointsToConstantInt()) {
                            edge.add(new JBCIntegerRelation(xR, IntegerRelationType.EQ, newXR.toLiteralInt()));
                        } else if (newYR.pointsToConstantInt()) {
                            edge.add(new JBCIntegerRelation(yR, IntegerRelationType.EQ, newYR.toLiteralInt()));
                        }
                        out.add(new Pair<State, EdgeInformation>(newState, edge));
                    }
                } else {
                    final AbstractVariableReference newXR = newState.createReferenceAndAdd(t.x, this.argumentT);
                    newState.replaceReference(xR, newXR);
                    Map<AbstractVariableReference, AbstractVariableReference> refRenaming = trimRelatedIntegers(Collections.singletonMap(newXR,
                            t.x),
                            newState);
                    if (!newState.getIntegerRelations().isContradictory()) {
                        if (refRenaming.containsKey(newXR)) {
                            refRenaming.put(xR, refRenaming.get(newXR));
                            refRenaming.remove(newXR);
                        } else {
                            refRenaming.put(xR, newXR);
                        }
                        out.add(new Pair<State, EdgeInformation>(newState, new RefinementEdge("", refRenaming)));
                    }
                }
            }
            return !out.isEmpty();
        }

        /* We can't decide it, we can't refine it, split it: */
        this.split(curState, y, xR, yR, out);
        return true;
    }

    /*
     * Let x=y=[-inf,inf], x<=y.
     * If we refine x to x'=[0,inf], then we get y'=[0,inf], too.
     */
    private Map<AbstractVariableReference, AbstractVariableReference>
            trimRelatedIntegers(Map<AbstractVariableReference, AbstractInt> refinedInts, State state) {
        Set<JBCIntegerRelation> relations = new LinkedHashSet<>(state.getIntegerRelations().getRelations());
        // add the mirrored relations, s.t. we just have to handle one direction, later
        Set<JBCIntegerRelation> toAdd = new LinkedHashSet<>();
        for (JBCIntegerRelation rel: relations) {
            toAdd.add(rel.mirror());
        }
        relations.addAll(toAdd);
        // the new value for a certain reference may change several times; keep track of these changes in this map
        Map<AbstractVariableReference, AbstractInt> replacementMap = new LinkedHashMap<>();
        for (JBCIntegerRelation rel: relations) {
            if (rel.rightIntegerIsNoRef()) {
                continue;
            }
            AbstractVariableReference leftRef = rel.getLeftIntRef();
            AbstractVariableReference rightRef = rel.getRightIntRef();
            if (!refinedInts.containsKey(leftRef)) {
                continue;
            }
            // the left reference has been refined, get the values
            AbstractInt oldLeftInt;
            if (replacementMap.containsKey(leftRef)) {
                oldLeftInt = replacementMap.get(leftRef);
            } else {
                oldLeftInt = refinedInts.get(leftRef);
            }
            AbstractInt oldRightInt;
            if (replacementMap.containsKey(rightRef)) {
                oldRightInt = replacementMap.get(rightRef);
            } else {
                oldRightInt = (AbstractInt) state.getAbstractVariable(rightRef);
            }
            if (oldLeftInt == null || oldRightInt == null) {
                // this happens if the relation tells us something about abstract array indices
                continue;
            }
            IntervalBound oldLowerBound = oldRightInt.getLower();
            IntervalBound oldUpperBound = oldRightInt.getUpper();
            IntervalBound newLowerBound = oldLowerBound;
            IntervalBound newUpperBound = oldUpperBound;
            switch (rel.getRelationType()) {
                case GE:
                    // [l1,u1]>=[l2,u2] => u2'=min(u1, u2)
                    newUpperBound = oldUpperBound.min(oldLeftInt.getUpper());
                    break;
                case GT:
                    // [l1,u1]>[l2,u2] => u2'=min(u1-1,u2)
                    newUpperBound = oldUpperBound.min(oldLeftInt.getUpper().add(IntervalBound.NEGONE));
                    break;
                case LE:
                    // [l1,u1]<=[l2,u2] => l2'=max(l1,l2)
                    newLowerBound = oldLowerBound.max(oldLeftInt.getLower());
                    break;
                case LT:
                    // [l1,u1]<[l2,u2] => l2'=max(l1+1,l2)
                    newLowerBound = oldLowerBound.max(oldLeftInt.getLower().add(IntervalBound.ONE));
                    break;
                default:
                    break;
            }
            // if some bound changed, construct the new value
            AbstractInt newRightInt = oldRightInt;
            if (!oldLowerBound.equals(newLowerBound)) {
                newRightInt = newRightInt.setLower(newLowerBound);
            }
            if (!oldUpperBound.equals(newUpperBound)) {
                newRightInt = newRightInt.setUpper(newUpperBound);
            }
            // if newRightInt == null, then this state is contradictory; here, we don't care about that
            if (newRightInt != null && !oldRightInt.equals(newRightInt)) {
                replacementMap.put(rightRef, newRightInt);
            }
        }
        // replace the references in the state
        Map<AbstractVariableReference, AbstractVariableReference> result = new LinkedHashMap<>();
        for (Entry<AbstractVariableReference, AbstractInt> e: replacementMap.entrySet()) {
            AbstractVariableReference oldRef = e.getKey();
            AbstractInt newVal = e.getValue();
            AbstractVariableReference newRef = state.createReferenceAndAdd(newVal, this.argumentT);
            state.replaceReference(oldRef, newRef);
            result.put(oldRef, newRef);
        }
        return result;
    }

    /**
     * Refines information needed to evaluate this branch opcode on address
     * information. Does existence and equality refinements.
     * @param s The old state.
     * @param out List of result states containing refined information.
     * @return a number of successor states created by either evaluation,
     * refinement or splitting.
     */
    private boolean addrRefine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        assert (this.argumentT == OperandType.ADDRESS && (this.compT == ComparisonType.NULL
            || this.compT == ComparisonType.NONNULL
            || this.compT == ComparisonType.EQ || this.compT == ComparisonType.NE)) : "Can only handle address comparisons with null here";

        final StackFrame curFrame = s.getCurrentStackFrame();

        if (this.compT == ComparisonType.NULL || this.compT == ComparisonType.NONNULL) {
            final AbstractVariableReference oR = curFrame.peekOperandStack(0);

            //If no refinement needs to be performed, evaluate the opcode:
            if (ObjectRefinement.forExistence(oR, s, out)) {
                return true;
            }
        } else {
            assert (this.compT == ComparisonType.EQ || this.compT == ComparisonType.NE) : "Unhandled address comparison";
            final AbstractVariableReference aR = curFrame.peekOperandStack(1);
            final AbstractVariableReference bR = curFrame.peekOperandStack(0);

            if (ObjectRefinement.forExistence(aR, s, out)) {
                return true;
            }
            if (ObjectRefinement.forExistence(bR, s, out)) {
                return true;
            }
            // Make sure we know whether a, b exist and are identical or not
            if (ObjectRefinement.forEquality(aR, bR, s, out, true)) {
                return true;
            }
        }

        return false;
    }

    /**
     * Try to decide the condition.
     * @param s the current state
     * @return Next state/Edge leading to it
     */
    private Pair<State, EvaluationEdge> addrEvaluate(final State s) {
        assert (this.argumentT == OperandType.ADDRESS && (this.compT == ComparisonType.NULL
            || this.compT == ComparisonType.NONNULL
            || this.compT == ComparisonType.EQ || this.compT == ComparisonType.NE)) : "Can only handle address comparisons with null here";

        final StackFrame curFrame = s.getCurrentStackFrame();

        //Handle comparisons with the NULL pointer:
        if (this.compT == ComparisonType.NULL || this.compT == ComparisonType.NONNULL) {
            final AbstractVariableReference oR = curFrame.peekOperandStack(0);

            final State newState = s.clone();
            final EvaluationEdge edge = new EvaluationEdge();
            //Get rid of the (used up) arguments:
            newState.getCurrentStackFrame().popOperandStack();

            //True case: We are testing for null and it is null or we are testing
            //           for nonnull and it exists:
            if ((oR.isNULLRef() && (this.compT == ComparisonType.NULL))
                || (!oR.isNULLRef() && (this.compT == ComparisonType.NONNULL)))
            {
                newState.getCurrentStackFrame().setCurrentOpCode(this.getBranchTarget());
                //False case: We are testing for null and it is nonnull or we are testing
                //            for null and it exists:
            } else if ((!oR.isNULLRef() && (this.compT == ComparisonType.NULL))
                || (oR.isNULLRef() && (this.compT == ComparisonType.NONNULL)))
            {
                newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());
            } else {
                assert (false) : "Interesting case of tri-state boolean logic noticed";
            }

            return new Pair<>(newState, edge);
        }
        assert (this.compT == ComparisonType.EQ || this.compT == ComparisonType.NE) : "Unhandled address comparison";
        final AbstractVariableReference aR = curFrame.peekOperandStack(1);
        final AbstractVariableReference bR = curFrame.peekOperandStack(0);

        if (s.getAllNRIRs().contains(aR) || s.getAllNRIRs().contains(bR)) {
            assert (false) : "NRIRs should not appear on the operand stack!";
        }

        if ((this.compT == ComparisonType.EQ && aR.equals(bR)) || (this.compT == ComparisonType.NE && !aR.equals(bR))) {
            final State newState = s.clone();
            newState.getCurrentStackFrame().popOperandStack();
            newState.getCurrentStackFrame().popOperandStack();
            newState.getCurrentStackFrame().setCurrentOpCode(this.getBranchTarget());
            return new Pair<>(newState, new EvaluationEdge());
        }
        final State newState = s.clone();
        newState.getCurrentStackFrame().popOperandStack();
        newState.getCurrentStackFrame().popOperandStack();
        newState.getCurrentStackFrame().setCurrentOpCode(this.getNextOp());
        return new Pair<>(newState, new EvaluationEdge());
    }

    /**
     * @return the short name for this OpCode, for use in the TRS encoding of
     * the symbolic evaluation.
     */
    @Override
    public String getShortName() {
        return this.compT.toString();
    }

    /** {@inheritDoc} */
    @Override
    public final Set<OpCode> getAllPossibleSuccessors() {
        final Set<OpCode> res = new LinkedHashSet<>();
        res.add(this.branchTarget);

        if (this.compT != ComparisonType.JMP || this.isSubroutine) {
            res.add(this.getNextOp());
        }

        return res;
    }

    /**
     * @return true iff this opcode is a goto opcode
     */
    public boolean isGoto() {
        return this.compT == ComparisonType.JMP;
    }

    /**
     * @return true iff this opcode is a JSR opcode
     */
    public boolean isJSR() {
        return this.isSubroutine;
    }

    /**{@inheritDoc}*/
    @Override
    public State reverseEvaluation(
        final State preEval,
        final State postEval,
        final State postEvalInst,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        final State preEvalInst = postEvalInst.clone();
        final StackFrame curAbstrFrame = preEval.getCurrentStackFrame();
        final StackFrame curInstFrame = preEvalInst.getCurrentStackFrame();
        curInstFrame.setCurrentOpCode(curAbstrFrame.getCurrentOpCode());

        //Now get the right number of arguments back onto the operand stack:
        if (this.compT == ComparisonType.JMP) {
            if (this.isSubroutine) {
                throw new NotYetImplementedException();
            }
        } else {
            switch (this.argumentT) {
            case INTEGER:
                if (this.comp2Args) {
                    AbstractVariableReference poppedRef = curAbstrFrame.peekOperandStack(1);
                    curInstFrame.pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, poppedRef, refMap));
                    poppedRef = curAbstrFrame.peekOperandStack(0);
                    curInstFrame.pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, poppedRef, refMap));
                } else {
                    final AbstractVariableReference poppedRef = curAbstrFrame.peekOperandStack(0);
                    curInstFrame.pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, poppedRef, refMap));
                }
                break;
            case ADDRESS:
                if (this.compT == ComparisonType.NULL || this.compT == ComparisonType.NONNULL) {
                    final AbstractVariableReference poppedRef = curAbstrFrame.peekOperandStack(0);
                    curInstFrame.pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, poppedRef, refMap));
                } else {
                    AbstractVariableReference poppedRef = curAbstrFrame.peekOperandStack(1);
                    curInstFrame.pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, poppedRef, refMap));
                    poppedRef = curAbstrFrame.peekOperandStack(0);
                    curInstFrame.pushOperandStack(State.mapOrCopyRef(preEval, preEvalInst, poppedRef, refMap));
                }
                break;
            default:
                assert (false) : "We can't handle anything but integers and addresses for now";
            }
        }
        return preEvalInst;
    }

    @Override
    public int getNumberOfArguments() {
        if (this.isSubroutine) {
            throw new NotYetImplementedException();
        }
        switch (compT) {
            case EQ:
            case GE:
            case GT:
            case LE:
            case LT:
            case NE:
                return comp2Args ? 2 : 1;
            case NONNULL:
            case NULL:
                return 1;
            case JMP:
                return 0;
            default: throw new RuntimeException();
        }
    }

    @Override
    public int getNumberOfOutputs() {
        if (this.isSubroutine) {
            throw new NotYetImplementedException();
        }
        return 0;
    }

}
