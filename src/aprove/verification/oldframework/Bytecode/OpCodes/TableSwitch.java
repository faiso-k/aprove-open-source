package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * The tableswitch opcode.
 * @author cotto
 */
public class TableSwitch extends OpCode {
    /**
     * The highest index of the table.
     */
    private final int high;

    /**
     * The lowest index of the table.
     */
    private final int low;

    /**
     * @return the highest index of the table
     */
    public int getHigh() {
        return this.high;
    }

    /**
     * @return the lowest index of the table
     */
    public int getLow() {
        return this.low;
    }

    /**
     * The actual table
     */
    private final OpCode[] offsets;

    /**
     * The default target
     */
    private OpCode def;

    /**
     * Store the default target
     * @param defParam the default target
     */
    public void setDefault(final OpCode defParam) {
        this.def = defParam;
    }

    /**
     * Create a new tableswitch opcode with the given high and low values
     * @param h the high index
     * @param l the low index
     */
    public TableSwitch(final int h, final int l) {
        this.high = h;
        this.low = l;
        this.offsets = new OpCode[(this.high - this.low + 1)];
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        final String s = "tableswitch (" + this.low + ".." + this.high + ")";
        return s;
    }

    /**
     * @param idx the index
     * @return the opcode for the given index.
     */
    private OpCode getTarget(final int idx) {
        if (idx < this.low || idx > this.high) {
            return this.def;
        }
        return this.offsets[idx - this.low];
    }

    /**
     * Set the target opcode for the given index.
     * @param idx the index
     * @param target the opcode
     */
    public void setTarget(final int idx, final OpCode target) {
        if (idx < this.low || idx > this.high) {
            this.def = target;
        } else {
            this.offsets[idx - this.low] = target;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> out) {
        final AbstractVariableReference ref = s.getCurrentStackFrame().getOperandStack().peek(0);
        final AbstractInt index = (AbstractInt) s.getAbstractVariable(ref);
        // Perhaps we have enough information to just evaluate? (this is ugly, I admit it)
        final Pair<State, EvaluationEdge> evalResult = this.evaluate(s);
        if (evalResult != null) {
            return false;
        }
        this.handleNonDeterministicCase(s, index, out);
        return true;
    }

    /**
     * Evaluate (if possible).
     * @param state the current state
     * @return the resulting state or null if deterministic evaluation is not
     * possible.
     */
    @Override
    public Pair<State, EvaluationEdge> evaluate(final State state) {
        // The index is at the top of the operand stack.
        final AbstractVariableReference ref = state.getCurrentStackFrame().getOperandStack().peek(0);
        final AbstractInt index = (AbstractInt) state.getAbstractVariable(ref);
        assert !ref.pointsToLong() : "According to JVMS 3 tableswitch index should be an int (no long)";

        if (index.isLiteral()) {
            final EvaluationEdge edge = new EvaluationEdge();
            edge.add(new JBCIntegerRelation(ref, IntegerRelationType.EQ, index.getLiteral().intValue()));
            return new Pair<>(this.setupState(state, index.getLiteral().intValue()), edge);
        }
        // Does the state enforce "i < low" or "i > high"?
        final SplitResult splitRes = state.getSplitResult();
        IntegerRelationType cmpResult = null;
        if (splitRes != null) {
            cmpResult = ((ComparisonSplitResult) splitRes).getCmpResult();
        }
        final AbstractInt tableLow = AbstractInt.create(this.low);
        final AbstractInt tableHigh = AbstractInt.create(this.high);
        State evalResult = null;
        final EvaluationEdge edge = new EvaluationEdge();
        final Integer compareApproxA = index.compareToApprox(tableLow);
        final Integer compareApproxB = index.compareToApprox(tableHigh);
        // If index is lower than tableLow or this information is in the split
        if ((compareApproxA != null && compareApproxA < 0) || cmpResult == IntegerRelationType.LT) {
            edge.add(new JBCIntegerRelation(ref, IntegerRelationType.LT, this.low));
            evalResult = this.setupState(state, this.def);
            return new Pair<>(evalResult, edge);
        } else if ((compareApproxB != null && compareApproxB > 0) || cmpResult == IntegerRelationType.GT) {
            edge.add(new JBCIntegerRelation(ref, IntegerRelationType.GT, this.high));
            evalResult = this.setupState(state, this.def);
            return new Pair<>(evalResult, edge);
        }
        // no literal and (even when considering the split result) not below and not above, so we need to refine
        return null;
    }

    /**
     * We do not know where to go, so we have to refine the index or split. This
     * results in a lot of branching, if the table is huge.
     * @param state the current state
     * @param index the (abstract) table index
     * @param result where to put the resulting states
     */
    private void handleNonDeterministicCase(
        final State state,
        final AbstractInt index,
        final Collection<Pair<State, ? extends EdgeInformation>> result)
    {
        assert (!index.isLiteral());

        final AbstractVariableReference oldIdxRef = state.getCurrentStackFrame().getOperandStack().peek(0);

        /*
         * Three intervals have to be watched: lower than low, higher than high,
         * and the things in between.
         */
        int middle = 0;
        /*
         * If the compare was null, we do not know anything. Thus we assume it
         * might be lower. If it is < 0 it actually was lower (all elements of
         * index). >= 0 means that there is no entry in index which is lower
         * than this.low.
         */
        boolean lower =
            !AbstractInt.computeComparisonResult(
                IntegerRelationType.GE,
                index,
                AbstractInt.create(this.low),
                false,
                false);
        // Same logic here
        boolean higher =
            !AbstractInt.computeComparisonResult(
                IntegerRelationType.LE,
                index,
                AbstractInt.create(this.high),
                false,
                false);
        if (state.getSplitResult() != null) {
            final ComparisonSplitResult compSplitRes = (ComparisonSplitResult) state.getSplitResult();
            if (compSplitRes.getCmpResult() == IntegerRelationType.EQ) {
                lower = false;
                higher = false;
            }
        }
        // Count the number of elements between higher and lower
        for (int i = this.low; i <= this.high; i++) {
            if (index.containsLiteral(i)) {
                middle++;
            }
        }
        // at least one outcome
        assert (lower || higher || middle > 0);
        // not only one outcome
        assert ((lower && higher) || (lower && middle == 1) || (middle == 1 && higher) || middle > 1);
        if (lower || higher) {
            // split
            if (lower) {
                final State newState = state.clone();
                newState.setSplitResult(new ComparisonSplitResult(IntegerRelationType.LT));
                final SplitEdge edge = new SplitEdge(Collections.singleton(oldIdxRef));
                result.add(new Pair<State, EdgeInformation>(newState, edge));
            }

            if (middle == 1) {
                // just one case possible, replace var with literal
                final SplitEdge edge = new SplitEdge(Collections.singleton(oldIdxRef));
                for (int i = this.low; i <= this.high; i++) {
                    if (index.containsLiteral(i)) {
                        final State newState = this.substituteIndex(state, AbstractInt.create(i));
                        edge.add(new JBCIntegerRelation(oldIdxRef, IntegerRelationType.EQ, i));
                        result.add(new Pair<>(newState, edge));
                    }
                }
            } else if (middle > 1) {
                // the different alternatives will be handled when refining the resulting state (again!)
                final State newState = state.clone();
                newState.setSplitResult(new ComparisonSplitResult(IntegerRelationType.EQ));
                final SplitEdge edge = new SplitEdge(Collections.singleton(oldIdxRef));
                result.add(new Pair<State, EdgeInformation>(newState, edge));
            }

            if (higher) {
                final State newState = state.clone();
                newState.setSplitResult(new ComparisonSplitResult(IntegerRelationType.GT));
                final SplitEdge edge = new SplitEdge(Collections.singleton(oldIdxRef));
                result.add(new Pair<State, EdgeInformation>(newState, edge));
            }
        } else {
            // refine, add a state for each possibility
            for (int i = this.low; i <= this.high; i++) {
                if (index.containsLiteral(i)) {
                    final State newState = state.clone();
                    final AbstractVariableReference ref =
                        newState.createReferenceAndAdd(AbstractInt.create(i), oldIdxRef.getPrimitiveType());

                    newState.replaceReference(oldIdxRef, ref);
                    final RefinementEdge edge = new RefinementEdge(oldIdxRef, ref);
                    result.add(new Pair<State, EdgeInformation>(newState, edge));
                }
            }
        }
    }

    /**
     * @param state the current state
     * @param target the new opcode
     * @return the new state where the new opcode is the given one.
     */
    private State setupState(final State state, final OpCode target) {
        final State newState = state.clone();
        newState.getCurrentStackFrame().getOperandStack().pop();
        newState.setCurrentOpCode(target);
        return newState;
    }

    /**
     * @param state the current state
     * @param idx the index in this table giving the new opcode
     * @return the new state where the new opcode is determined by the given
     * index.
     */
    private State setupState(final State state, final int idx) {
        return this.setupState(state, this.getTarget(idx));
    }

    /**
     * @param state the current state
     * @param newInt the new value for the index
     * @return a new state where the table index is replaced by the given value.
     */
    private State substituteIndex(final State state, final AbstractInt newInt) {
        final State newState = state.clone();
        final AbstractVariableReference ref = newState.createReferenceAndAdd(newInt, OperandType.INTEGER);
        newState.replaceReference(state.getCurrentStackFrame().getOperandStack().peek(0), ref);
        return newState;
    }

    /** {@inheritDoc} */
    @Override
    public final Set<OpCode> getAllPossibleSuccessors() {
        final Set<OpCode> res = new LinkedHashSet<>();

        res.add(this.def);

        for (final OpCode opc : this.offsets) {
            if (opc != null) {
                res.add(opc);
            }
        }

        return res;
    }

    @Override
    public int getNumberOfArguments() {
        return 1;
    }

    @Override
    public int getNumberOfOutputs() {
        return 0;
    }

}
