/**
 *
 * @author christian
 */

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

public class LookupSwitch extends OpCode {
    /**
     * The base address is the address of this opcode. The offsets will be added
     * to this value.
     */
    private final int base;

    /**
     * Number of matcher pairs.
     */
    private final int npairs;

    public int getNpairs() {
        return this.npairs;
    }

    private final Pair[] pairs;
    private OpCode def;

    public OpCode getDefault() {
        return this.def;
    }

    public void setDefault(final OpCode def) {
        this.def = def;
    }

    /**
     * Just a struct like class for a pair of match and opcode.
     */
    private static class Pair {
        public OpCode target;
        public int match;
    };

    public LookupSwitch(final int b, final int n) {
        this.base = b;
        this.npairs = n;
        this.pairs = new Pair[n];
    }

    public OpCode getTarget(final int key) {
        for (int i = 0; i < this.npairs && this.pairs[i].match <= key; i += 1) {
            if (this.pairs[i].match == key) {
                return this.pairs[i].target;
            }
        }
        return this.def;
    }

    /**
     * @return all possible targets (including default)
     */
    public OpCode[] getAllTargets() {
        final OpCode[] targets = new OpCode[this.npairs + 1];
        for (int i = 0; i < this.npairs; i++) {
            targets[i] = this.pairs[i].target;
        }
        targets[this.npairs] = this.getDefault();
        return targets;
    }

    public void setTarget(final int idx, final int match, final OpCode target) {
        this.pairs[idx] = new Pair();
        this.pairs[idx].match = match;
        this.pairs[idx].target = target;
    }

    @Override
    public String toString() {
        final StringBuilder s = new StringBuilder();
        s.append("lookupswitch (base: ").append(this.base);
        s.append(" default: ").append(this.def);
        s.append(" npairs: ").append(this.npairs + ")\n");
        s.append("\tdefault: ").append(this.def + "\n");
        for (int i = 0; i < this.npairs; i++) {
            s.append("\t");
            s.append(this.pairs[i].match).append(": ");
            s.append(this.pairs[i].target).append("\n");
        }
        return s.toString();
    }

    @Override
    public aprove.verification.oldframework.Utility.GenericStructures.Pair<State, EvaluationEdge> evaluate(final State state) {
        // the next state can be calculated deterministically
        // if this is false, then we know, that no pair matches the integer
        final State newState = state.clone();

        final SplitResult splitRes = state.getSplitResult();
        if (splitRes != null) {
            if (Globals.useAssertions) {
                assert (!((BooleanSplitResult) splitRes).getTruthValue());
            }
            newState.setCurrentOpCode(this.getDefault());
            newState.getCurrentStackFrame().popOperandStack();

            // otherwise, there has to be exactly one matching pair
        } else {
            // Get the key from the stack
            final AbstractVariableReference ref = state.getCurrentStackFrame().getOperandStack().peek(0);
            final AbstractInt integer = (AbstractInt) state.getAbstractVariable(ref);
            final Collection<Integer> matches = this.findMatches(integer);
            if (Globals.useAssertions) {
                assert ref.pointsToAnyIntegerType() : "Key in lookup switch must be an int";
                // either we hit exactly one key or none at all
                assert (matches.size() < 2);
            }
            newState.getCurrentStackFrame().popOperandStack();

            if (matches.isEmpty()) {
                newState.setCurrentOpCode(this.def);
            } else {
                assert (integer.isLiteral());
                newState.setCurrentOpCode(this.getTarget(integer.getLiteral().intValue()));
            }
        }

        return new aprove.verification.oldframework.Utility.GenericStructures.Pair<>(newState, new EvaluationEdge());
    }

    /**
     * Constructs deterministic states from the given one. This means:<br>
     * If the top opstack element is a literal, or if the interval representing
     * that element contains none of the pairs, then nothing happens, as the
     * state is deterministic, then. Otherwise, new states are created as
     * follows:
     * <ul>
     * <li>For each pair, whose match value is contained in the interval
     * representing the top stack element, one new state is created, with the
     * stop stack element being replaced by an appropriate literal, and
     * IntegerRelation variable information added to the edge accordingly.</li>
     * <li>One new state, with a fresh variable at the top of the opstack, and
     * an edge, which specifies that the old variable is not equal to any of the
     * matched pairs</li>
     * </ul>
     * @param state the current state
     * @param nextStates deterministic states will be inserted here
     * @return true iff deterministic states were created. false, if the state
     * was deterministic
     */
    @Override
    public boolean refine(
        final State state,
        final Collection<aprove.verification.oldframework.Utility.GenericStructures.Pair<State, ? extends EdgeInformation>> nextStates)
    {
        final AbstractVariableReference ref = state.getCurrentStackFrame().getOperandStack().peek(0);
        final AbstractInt integer = (AbstractInt) state.getAbstractVariable(ref);
        if (integer.isLiteral() || state.getSplitResult() != null) {
            return false;
        }

        // find all keys that could be hit by the abstract key
        final Collection<Integer> matches = this.findMatches(integer);

        if (matches.isEmpty()) {
            /*
             * None of the represented values hits any key, so we have to use
             * the default case.
             */
            return false;
        }

        // Add matching cases
        for (final Integer i : matches) {
            final LiteralInt newInt = AbstractInt.create(i);
            final State newState = state.clone();
            final AbstractVariableReference newIntRef = newState.createReferenceAndAdd(newInt, ref.getPrimitiveType());
            newState.replaceReference(ref, newIntRef);
            final RefinementEdge edge = new RefinementEdge(ref, newIntRef);
            edge.add(new JBCIntegerRelation(ref, IntegerRelationType.EQ, newInt));
            nextStates.add(new aprove.verification.oldframework.Utility.GenericStructures.Pair<State, EdgeInformation>(newState, edge));
        }
        /* Add non-matching case:
         * Create a new reference with the old value and use the split result to
         * enforce the default case.
         */
        final State newState = state.clone();
        final AbstractVariableReference newIntRef = newState.createReferenceAndAdd(integer, ref.getPrimitiveType());
        newState.replaceReference(ref, newIntRef);
        final RefinementEdge edge = new RefinementEdge(ref, newIntRef);
        for (final Integer i : matches) {
            final LiteralInt newInt = AbstractInt.create(i);
            edge.add(new JBCIntegerRelation(ref, IntegerRelationType.NE, newInt));
        }

        newState.setSplitResult(new BooleanSplitResult(false));
        nextStates.add(new aprove.verification.oldframework.Utility.GenericStructures.Pair<State, EdgeInformation>(newState, edge));
        return true;
    }

    /**
     * @param key the key used in the lookup
     * @return the matches that are covered by the given abstract key. In other
     * words, this is an overapproximation of all possible matches.
     */
    private Collection<Integer> findMatches(final AbstractInt key) {
        final Collection<Integer> result = new ArrayList<>(this.npairs);
        for (final Pair pair : this.pairs) {
            if (key.containsLiteral(pair.match)) {
                result.add(pair.match);
            }
        }
        return result;
    }

    /** {@inheritDoc} */
    @Override
    public final Set<OpCode> getAllPossibleSuccessors() {
        final Set<OpCode> res = new LinkedHashSet<>();

        res.add(this.def);

        for (final Pair p : this.pairs) {
            if (p != null) {
                res.add(p.target);
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
