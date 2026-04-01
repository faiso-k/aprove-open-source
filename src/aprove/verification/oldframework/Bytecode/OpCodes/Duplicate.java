package aprove.verification.oldframework.Bytecode.OpCodes;

import java.util.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of dup* calls on the operand stack.
 * <br>
 * This is embarrassingly complex because we've ignored the usual way of
 * using two words (4 bytes) to represent long/double values, and have instead
 * decided to just work on values (thus collapsing the two words making up a
 * long into a single value). While most operations are actually easier that
 * way, the word-oriented semantics of the dup family of opcodes are harder to
 * implement.
 *
 * @author Christian von Essen, Marc Brockschmidt
 */
public class Duplicate extends OpCode {
    /**
     * Number of words that should be duplicated (either one or two, where
     * the latter can either mean two one-word values or one two-word value)
     */
    private final int wordsToDuplicate;

    /**
     * Number of words to skip (counted from the stack top) before inserting
     * the duplicated values again onto the stack. This is counted in words,
     * thus a value of 4 may correspond to two long values, one long and two
     * normal values or even four normal, one-word values.
     */
    private final int wordsToSkipWhenInserting;

    /**
     * @param wordsToDup Number of words to duplicate on the operand stack.
     * @param wordsToSkip Number of words to skip (counted from the stack top)
     *  before inserting the duplicated values.
     */
    public Duplicate(final int wordsToDup, final int wordsToSkip) {
        this.wordsToDuplicate = wordsToDup;
        this.wordsToSkipWhenInserting = wordsToSkip;
    }

    /** {@inheritDoc} */
    @Override
    public final Pair<State, EvaluationEdge> evaluate(final State state) {
        final State newState = state.clone();

        //Get data:
        final StackFrame curFrame = newState.getCurrentStackFrame();

        //Get the stack top under which the duplicated values will be inserted:
        final LinkedList<AbstractVariableReference> stackTop = new LinkedList<>();
        int poppedStackWords = 0;
        while (poppedStackWords < this.wordsToSkipWhenInserting) {
            final AbstractVariableReference topRef = curFrame.popOperandStack();
            stackTop.addLast(topRef);

            //count how many values we have moved off the top until now:
            poppedStackWords += topRef.getPrimitiveType().getWords();
        }
        assert (poppedStackWords == this.wordsToSkipWhenInserting) : "Was supposed to skip "
            + this.wordsToSkipWhenInserting
            + " when duplicating, but could only pop "
            + poppedStackWords
            + " words";

        //We now have all the data to keep, now re-add the values we need to duplicate:
        int duplicatedWords = 0;
        int index = 0;
        while (duplicatedWords < this.wordsToDuplicate) {
            /* We take the i-th value and re-add it to the end of stackTop, which
             * will be pushed onto the stack in reversed order. If [1 2 3 4] is
             * the popped 4 one-word value stack top, and we want to dup two words,
             * we have [1 2 3 4] -> [1 2 3 4 1] -> [1 2 3 4 1 2]. The latter is
             * put (in reversed order) onto the operand stack [ ... ], such that
             * we finally get [ ... 2 1 4 3 2 1 ].
             */
            final AbstractVariableReference dupRef = stackTop.get(index);
            stackTop.addLast(dupRef);

            //count how many words we actually duplicated until now:
            duplicatedWords += dupRef.getPrimitiveType().getWords();
            index++;
        }
        assert (duplicatedWords == this.wordsToDuplicate) : "Was supposed to duplicate "
            + this.wordsToDuplicate
            + ", but could only dup "
            + duplicatedWords
            + " words";

        //Now push everything back onto the stack:
        final Iterator<AbstractVariableReference> it = stackTop.descendingIterator();
        while (it.hasNext()) {
            curFrame.pushOperandStack(it.next());
        }

        //Now finish, move through the code:
        curFrame.setCurrentOpCode(this.getNextOp());

        final EvaluationEdge info = new EvaluationEdge();
        return new Pair<>(newState, info);
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return "DUP";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public State reverseEvaluation(
        final State preEval,
        final State postEval,
        final State postEvalInst,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        final State preEvalInst = postEvalInst.clone();
        final StackFrame curInstFrame = preEvalInst.getCurrentStackFrame();

        // Save those references away which were not changed by the DUP:
        final LinkedList<AbstractVariableReference> stackTop = new LinkedList<>();
        int poppedStackWords = 0;
        while (poppedStackWords < this.wordsToSkipWhenInserting) {
            final AbstractVariableReference topRef = curInstFrame.popOperandStack();
            stackTop.addLast(topRef);

            //count how many values we have moved off the top until now:
            poppedStackWords += topRef.getPrimitiveType().getWords();
        }

        // Remove those words that were duplicated:
        int deduplicatedWords = 0;
        while (deduplicatedWords < this.wordsToDuplicate) {
            final AbstractVariableReference topRef = curInstFrame.popOperandStack();
            deduplicatedWords += topRef.getPrimitiveType().getWords();
        }

        //Now push the unchanged references back onto the stack:
        final Iterator<AbstractVariableReference> it = stackTop.descendingIterator();
        while (it.hasNext()) {
            curInstFrame.pushOperandStack(it.next());
        }

        curInstFrame.setCurrentOpCode(preEval.getCurrentOpCode());

        this.handleActiveVarChangesInRevEv(preEval, preEvalInst, postEval, refMap);

        return preEvalInst;
    }

    @Override
    public int getNumberOfArguments() {
        return 1;
    }

    @Override
    public int getNumberOfOutputs() {
        return 2;
    }

}
