package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * CMP opcode. It takes the two top-most values ... v1, v2 from
 * the stack and performs a comparison. If v1 > v2, 1 is pushed onto the
 * stack, for = a 0 is pushed and for v1 < v2 a -1.
 * @author Carsten Otto, Marc Brockschmidt
 */
public class Cmp extends OpCode {
    /**
     * Possible results of a comparison:
     */
    private static final Collection<IntegerRelationType> POSSIBLE_RESULTS = new LinkedHashSet<>(3);

    static {
        Cmp.POSSIBLE_RESULTS.add(IntegerRelationType.LT);
        Cmp.POSSIBLE_RESULTS.add(IntegerRelationType.GT);
        Cmp.POSSIBLE_RESULTS.add(IntegerRelationType.EQ);
    }

    /**
     * The type of the arguments.
     */
    private final OperandType type;

    /**
     * Create a new CMP opcode.
     *
     * @param typeParam the type if the arguments
     */
    public Cmp(final OperandType typeParam) {
        assert (typeParam == OperandType.LONG || typeParam == OperandType.FLOAT || typeParam == OperandType.DOUBLE) : "CMP may only be used for long, float and double values.";
        this.type = typeParam;
    }

    /**
     * Return a clone where the operand stack is changed according to the given
     * result.
     * @param state the current state
     * @param rel the result of evaluating the CMP opcode
     * @return the resulting state
     */
    private Pair<State, EvaluationEdge> construct(final State state, final IntegerRelationType rel) {
        final State newState = state.clone();
        final StackFrame topFrame = newState.getCurrentStackFrame();
        final AbstractVariableReference value2 = topFrame.popOperandStack();
        final AbstractVariableReference value1 = topFrame.popOperandStack();
        AbstractNumber resultVar = null;
        switch (rel) {
        case LT:
            resultVar = AbstractInt.getMOne();
            break;
        case EQ:
            resultVar = AbstractInt.getZero();
            break;
        case GT:
            resultVar = AbstractInt.getOne();
            break;
        default:
            assert (false) : "Illegal comparison result";
            break;
        }

        if (this.type == OperandType.LONG) {
            /*
             * This additional information can only be provided for type long,
             * not float/double.
             */
            final AbstractInt int1 = (AbstractInt) state.getAbstractVariable(value1);
            final AbstractInt int2 = (AbstractInt) state.getAbstractVariable(value2);
            Branch.addEdgeInfo(state, new EvaluationEdge(), value1, rel, value2, int2);
            if (int1 instanceof LiteralInt) {
                int2.noteComparisonWith(rel.mirror(), ((LiteralInt) int1).getLiteral());
            }
            if (int2 instanceof LiteralInt) {
                int1.noteComparisonWith(rel, ((LiteralInt) int2).getLiteral());
            }
        }
        final AbstractVariableReference result = newState.createReferenceAndAdd(resultVar, OperandType.INTEGER);
        topFrame.pushOperandStack(result);
        newState.setCurrentOpCode(this.getNextOp());
        return new Pair<>(newState, new EvaluationEdge());
    }

    /**
     * Evaluate a CMP working on integers.
     * @param state the current state
     * @return the resulting state
     */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State state) {
        // Did we enforce the result due to a SPLIT?
        final SplitResult splitRes = state.getSplitResult();
        IntegerRelationType cmpResult = null;
        if (splitRes != null) {
            cmpResult = ((ComparisonSplitResult) splitRes).getCmpResult();
        }

        if (cmpResult != null) {
            return this.construct(state, cmpResult);
        }

        // Try to evaluate
        final StackFrame curFrame = state.getCurrentStackFrame();
        final AbstractVariableReference yR = curFrame.peekOperandStack(0);
        final AbstractVariableReference xR = curFrame.peekOperandStack(1);

        if (this.type == OperandType.LONG) {
            final AbstractInt x = (AbstractInt) state.getAbstractVariable(xR);
            final AbstractInt y = (AbstractInt) state.getAbstractVariable(yR);

            final boolean sameRef = xR.equals(yR);
            final boolean areUnequal =
                state.checkIntegerRelation(xR, IntegerRelationType.NE, yR)
                    || state.checkIntegerRelation(xR, IntegerRelationType.LT, yR)
                    || state.checkIntegerRelation(xR, IntegerRelationType.GT, yR);
            for (final IntegerRelationType rel : POSSIBLE_RESULTS) {
                if (AbstractInt.computeComparisonResult(rel, x, y, sameRef, areUnequal)) {
                    return this.construct(state, rel);
                }
            }
        } else {
            final AbstractFloat x = (AbstractFloat) state.getAbstractVariable(xR);
            final AbstractFloat y = (AbstractFloat) state.getAbstractVariable(yR);
            assert (x.isLiteral());
            assert (y.isLiteral());
            final int compareResult = Double.compare(x.getLiteral(), y.getLiteral());
            IntegerRelationType rel;
            switch (compareResult) {
            case -1:
                rel = IntegerRelationType.LT;
                break;
            case 0:
                rel = IntegerRelationType.EQ;
                break;
            case 1:
                rel = IntegerRelationType.GT;
                break;
            default:
                assert (false);
                rel = null;
            }
            return this.construct(state, rel);
        }
        assert (false) : "This shouldn't be reachable";
        return null;
    }

    /**
     * @param state
     * @param out
     * @return
     */
    private boolean floatDoubleRefine(final State state, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        final StackFrame curFrame = state.getCurrentStackFrame();

        final AbstractVariableReference yR = curFrame.peekOperandStack(0);
        final AbstractVariableReference xR = curFrame.peekOperandStack(1);

        //Get the actual values, check if we have exactly one of the cases:
        final AbstractFloat x = (AbstractFloat) state.getAbstractVariable(xR);
        final AbstractFloat y = (AbstractFloat) state.getAbstractVariable(yR);
        if (x.isLiteral() && y.isLiteral()) {
            return false;
        }
        this.split(state, out, xR, POSSIBLE_RESULTS, yR);
        return true;
    }

    /**
     * Generates a number of new states from a current state, by splitting the
     * variable ranges in a way that allows to decide, or, as last resort, by
     * simply generating successors for the three possible results.
     *
     * @param state The old state
     * @param out list of successor states created by refinement or splitting.
     * @return true iff refinement was needed.
     */
    private boolean longRefine(final State state, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        final StackFrame curFrame = state.getCurrentStackFrame();

        final AbstractVariableReference yR = curFrame.peekOperandStack(0);
        final AbstractVariableReference xR = curFrame.peekOperandStack(1);
        if (Globals.useAssertions) {
            assert (xR.pointsToLong() && yR.pointsToLong()) : "CMP opcode used for non-long integer values.";
        }

        //Get the actual values, check if we have exactly one of the cases:
        final AbstractInt x = (AbstractInt) state.getAbstractVariable(xR);
        final AbstractInt y = (AbstractInt) state.getAbstractVariable(yR);

        final Collection<IntegerRelationType> possibleResults = new LinkedHashSet<>(POSSIBLE_RESULTS);

        final boolean areUnequal =
            state.checkIntegerRelation(xR, IntegerRelationType.NE, yR)
                || state.checkIntegerRelation(xR, IntegerRelationType.LT, yR)
                || state.checkIntegerRelation(xR, IntegerRelationType.GT, yR);
        final boolean sameRef = xR.equals(yR);
        for (final IntegerRelationType rel : possibleResults) {
            if (AbstractInt.computeComparisonResult(rel, x, y, sameRef, areUnequal)) {
                return false;
            }
        }

        /*
         * OK, no luck, we need to refine. First check if we can already rule
         * out one of the cases. possibleResults holds the set of integer
         * relations which might be true at this time. We first assume that
         * all are OK and then try to rule some out:
         */
        if (AbstractInt.computeComparisonResult(IntegerRelationType.GE, x, y, sameRef, areUnequal)) {
            possibleResults.remove(IntegerRelationType.LT);
        }
        if (AbstractInt.computeComparisonResult(IntegerRelationType.NE, x, y, sameRef, areUnequal)) {
            possibleResults.remove(IntegerRelationType.EQ);
        }
        if (AbstractInt.computeComparisonResult(IntegerRelationType.LE, x, y, sameRef, areUnequal)) {
            possibleResults.remove(IntegerRelationType.GT);
        }
        assert (possibleResults.size() >= 2);

        /*
         * Now try to refine the values for each of the cases. As soon as some
         * refinement actually helps, do the refinement and see what happens.
         */
        for (final IntegerRelationType rel : possibleResults) {
            final Collection<Pair<AbstractInt, AbstractInt>> result = IntegerRefinement.forIntegerRelation(x, y, rel);
            if (result != null) {
                for (final Pair<AbstractInt, AbstractInt> pair : result) {
                    final State newState = state.clone();
                    final AbstractVariableReference newXR = newState.createReferenceAndAdd(pair.x, this.type);
                    final AbstractVariableReference newYR = newState.createReferenceAndAdd(pair.y, this.type);
                    newState.replaceReference(xR, newXR);
                    newState.replaceReference(yR, newYR);
                    final LinkedHashMap<AbstractVariableReference, AbstractVariableReference> refRenaming =
                        new LinkedHashMap<>();
                    refRenaming.put(xR, newXR);
                    refRenaming.put(yR, newYR);
                    out.add(new Pair<State, EdgeInformation>(newState, new RefinementEdge("", refRenaming)));
                }
                return true;
            }
        }

        // Well, that did not help. Split then.
        this.split(state, out, xR, possibleResults, yR);
        return true;
    }

    /**
     * Generates a number of new states from a current state, by splitting the
     * variable ranges in a way that allows to decide, or, as last resort, by
     * simply generating successors for the tree possible results.
     *
     * @param state The old state
     * @param out list of successor states created by refinement or splitting.
     * @return true iff refinement was needed.
     */
    @Override
    public boolean refine(final State state, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        // If we already decided for a split, don't try to refine:
        if (state.getSplitResult() != null) {
            return false;
        }

        if (this.type == OperandType.LONG) {
            return this.longRefine(state, out);
        }
        return this.floatDoubleRefine(state, out);
    }

    /**
     * Create split successor states.
     * @param state the current states
     * @param newStates the resulting states will be stored here
     * @param possibleResults the relations that are possible
     */
    private void split(
        final State state,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates,
        final AbstractVariableReference left,
        final Collection<IntegerRelationType> possibleResults,
        final AbstractVariableReference right)
    {
        Set<AbstractVariableReference> involvedRefs = new LinkedHashSet<>();
        involvedRefs.add(left);
        involvedRefs.add(right);
        for (final IntegerRelationType rel : possibleResults) {
            final State newState = state.clone();
            newState.setSplitResult(new ComparisonSplitResult(rel));
            SplitEdge e = new SplitEdge(involvedRefs);
            if (left.pointsToAnyIntegerType() && right.pointsToAnyIntegerType()) {
                e.add(new JBCIntegerRelation(left, rel, right));
                newState.getIntegerRelations().note(left, rel, right);
            }
            newStates.add(new Pair<State, EdgeInformation>(newState, e));
        }
    }

    /**
     * @return a very nice string representation
     */
    @Override
    public String toString() {
        return "cmp (" + this.type + ")";
    }

    @Override
    public int getNumberOfArguments() {
        return 2;
    }

    @Override
    public int getNumberOfOutputs() {
        return 1;
    }

}
