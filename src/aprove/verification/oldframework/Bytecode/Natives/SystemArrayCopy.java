package aprove.verification.oldframework.Bytecode.Natives;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Implementation of the arraycopy() method.
 *
 * Exceptions:
 *   IndexOutOfBoundsException  if copying would cause access of data outside
 *                              array bounds.
 *   ArrayStoreException        if an element in the <code>src</code>
 *                              array could not be stored into the <code>dest
 *                              </code> array because of a type mismatch.
 *   NullPointerException       if either <code>src</code> or <code>dest</code>
 *                              is <code>null</code>.
 *
 * @author Marc Brockschmidt
 */
public class SystemArrayCopy extends PredefinedMethod {
    /** { @inheritDoc } */
    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(final State s) {
        //Get all data:
        final StackFrame curFrame = s.getCurrentStackFrame();
        final AbstractVariableReference srcRef = curFrame.peekOperandStack(4);
        final AbstractVariableReference srcPosRef = curFrame.peekOperandStack(3);
        final AbstractVariableReference destRef = curFrame.peekOperandStack(2);
        final AbstractVariableReference destPosRef = curFrame.peekOperandStack(1);
        final AbstractVariableReference lengthRef = curFrame.peekOperandStack(0);
        final List<OverflowInformation> overflowInformations = new LinkedList<>();

        //Prepare the new state
        final State newState = s.clone();

        if (srcRef.isNULLRef() || destRef.isNULLRef()) {
            OpCode.throwException(newState, NPE_EXC);
            return new Pair<>(newState, new MethodStartEdge());
        }

        final Array srcArr = (Array) s.getAbstractVariable(srcRef);
        final AbstractInt srcPosInt = (AbstractInt) s.getAbstractVariable(srcPosRef);
        final Array destArr = (Array) s.getAbstractVariable(destRef);
        final AbstractInt destPosInt = (AbstractInt) s.getAbstractVariable(destPosRef);
        final AbstractInt lengthInt = (AbstractInt) s.getAbstractVariable(lengthRef);

        if (needsIOOBE(s)) {
            OpCode.throwException(newState, Important.ARRAYINDEXOOB_EXC);
            final MethodStartEdge edge = new MethodStartEdge();
            for (final OverflowInformation overflowInformation : overflowInformations) {
                edge.add(overflowInformation);
            }
            return new Pair<>(newState, edge);
        }

        //OK, actually perform this. First, get rid of the arguments:
        for (int i = 0; i < 5; i++) {
            newState.getCurrentStackFrame().popOperandStack();
        }

        final LinkedHashSet<DefiniteReachabilityAnnotationCreation> newDefReach = new LinkedHashSet<>();
        //If we have the actual data, use it:
        if (srcArr instanceof ConcreteArray && srcPosInt.isLiteral() && lengthInt.isLiteral()) {
            final int length = lengthInt.getLiteral().intValue();
            final AbstractVariableReference[] valueRefs = new AbstractVariableReference[length];
            final int startPos = srcPosInt.getLiteral().intValue();
            final int endPos = srcPosInt.getLiteral().intValue() + length;

            //Get all value refs:
            for (int index = startPos; index < endPos; index++) {
                valueRefs[index - startPos] = ((ConcreteArray) srcArr).get(newState, srcRef, index);
            }

            //Put them into the new array:
            for (int index = 0; index < length; index++) {
                AbstractInt destPosPlusIndex = destPosInt.add(AbstractInt.create(index), IntegerType.JAVA_INT);
                final AbstractVariableReference indexRef =
                    newState.createReferenceAndAdd(destPosPlusIndex, OperandType.INTEGER);
                final AbstractVariable value = s.getAbstractVariable(valueRefs[index]);
                final boolean isPrimitive = value instanceof AbstractNumber;
                newDefReach.addAll(destArr.store(newState, destRef, indexRef, valueRefs[index], isPrimitive));
            }
            //Emulate a copy: Transport all annotations:
        } else {
            // the index is between pos and pos+length, construct abstract integer for that
            AbstractInt destPosPlusLength = destPosInt.add(lengthInt, IntegerType.JAVA_INT);
            final AbstractNumberMergeResult mergeResult =
                destPosInt.merge(destPosPlusLength, true, IntegerType.JAVA_INT);
            final AbstractNumber indexMerged = mergeResult.getMergedVariable();
            final AbstractVariableReference indexRef = newState.createReferenceAndAdd(indexMerged, OperandType.INTEGER);

            // load from (unknown) position
            final AbstractVariableReference loaded = srcArr.load(newState, srcRef, indexRef);

            // the content and index references must survive a gc()
            newState.getCurrentStackFrame().getOperandStack().push(loaded);
            newState.getCurrentStackFrame().getOperandStack().push(indexRef);

            // store into (unknown) position
            newDefReach.addAll(destArr.store(newState, destRef, indexRef, loaded, !loaded.pointsToReferenceType()));

            // pop "loaded" and "indexRef"
            newState.getCurrentStackFrame().getOperandStack().pop();
            newState.getCurrentStackFrame().getOperandStack().pop();
        }

        newState.getCurrentStackFrame().setCurrentOpCode(s.getCurrentOpCode().getNextOp());
        EvaluationEdge edge;
        switch (s.getTerminationGraph().getGoal()) {
            case UserDefined:
                edge = new PredefinedMethodEdge(
                        SimplePolynomial.ZERO,
                        SimplePolynomial.ZERO,
                        SimplePolynomial.ZERO,
                        SimplePolynomial.ZERO,
                        true,
                        true,
                        5);
                break;
            default:
                edge = new PredefinedMethodEdge(
                        SimplePolynomial.ONE,
                        SimplePolynomial.create(srcRef.toString()),
                        SimplePolynomial.ZERO,
                        SimplePolynomial.ZERO,
                        true,
                        true,
                        5);
        }
        edge.addAll(newDefReach);
        for (final OverflowInformation overflowInformation : overflowInformations) {
            edge.add(overflowInformation);
        }
        return new Pair<>(newState, edge);
    }

    /** { @inheritDoc } */
    @Override
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> result) {
        //We had a split already:
        if (s.getSplitResult() != null) {
            if (needsIOOBE(s) && ObjectRefinement.forInitialization(Important.ARRAYINDEXOOB_EXC, s, result)) {
                return true;
            } else {
                return false;
            }
        }
        final ClassPath cPath = s.getClassPath();

        //Get all data:
        final StackFrame curFrame = s.getCurrentStackFrame();
        final AbstractVariableReference srcRef = curFrame.peekOperandStack(4);
        final AbstractVariableReference destRef = curFrame.peekOperandStack(2);

        //Check for null pointers, ensure that the arrays exist:
        if (ObjectRefinement.forExistence(srcRef, s, result) || ArrayRefinement.forArrayRealization(srcRef, s, result))
        {
            return true;
        }
        if ((srcRef.isNULLRef() || destRef.isNULLRef()) && ObjectRefinement.forInitialization(Important.NPE_EXC, s, result)) {
            return true;
        }
        if (ObjectRefinement.forExistence(destRef, s, result)
            || ArrayRefinement.forArrayRealization(destRef, s, result))
        {
            return true;
        }

        if (srcRef.isNULLRef() || destRef.isNULLRef()) {
            return false;
        }

        if (needsIOOBE(s)) {
            //OK, computing if we need to throw an exception failed. Do the split:
            final State newIOOBExcState = s.clone();
            newIOOBExcState.setSplitResult(new BooleanSplitResult(true));
            result.add(new Pair<State, EdgeInformation>(newIOOBExcState, new SplitEdge(Collections
                    .singleton(destRef))));
            final State newNoIOOBExcState = s.clone();
            newNoIOOBExcState.setSplitResult(new BooleanSplitResult(false));
            result.add(new Pair<State, EdgeInformation>(newNoIOOBExcState, new SplitEdge(Collections.singleton(destRef))));
        }

        //OK, I just don't want to deal with this right now:
        assert (s.getAbstractType(srcRef).isAssignmentCompatibleTo(s.getAbstractType(destRef), cPath));
        return true;
    }

    private boolean needsIOOBE(State s) {
        BooleanSplitResult splitResult = (BooleanSplitResult) s.getSplitResult();
        if (splitResult != null) {
            return splitResult.getTruthValue();
        }

        final StackFrame curFrame = s.getCurrentStackFrame();
        final AbstractVariableReference srcRef = curFrame.peekOperandStack(4);
        final AbstractVariableReference srcPosRef = curFrame.peekOperandStack(3);
        final AbstractVariableReference destRef = curFrame.peekOperandStack(2);
        final AbstractVariableReference destPosRef = curFrame.peekOperandStack(1);
        final AbstractVariableReference lengthRef = curFrame.peekOperandStack(0);

        final Array srcArr = (Array) s.getAbstractVariable(srcRef);
        final AbstractInt srcPosInt = (AbstractInt) s.getAbstractVariable(srcPosRef);
        final Array destArr = (Array) s.getAbstractVariable(destRef);
        final AbstractInt destPosInt = (AbstractInt) s.getAbstractVariable(destPosRef);
        final AbstractInt lengthInt = (AbstractInt) s.getAbstractVariable(lengthRef);
        final AbstractInt srcArrLength = (AbstractInt) s.getAbstractVariable(srcArr.getLength());
        final AbstractInt destArrLength = (AbstractInt) s.getAbstractVariable(destArr.getLength());

        final boolean srcPosLTZero = srcPosInt.isNegative();
        final boolean destPosLTZero = destPosInt.isNegative();
        final boolean lengthLTZero = lengthInt.isNegative();
        AbstractInt srcPosPlusLength = srcPosInt.add(lengthInt, IntegerType.JAVA_INT);
        Integer cmpResult = srcPosPlusLength.compareToApprox(srcArrLength);
        final boolean srcPosLTBound = cmpResult != null && cmpResult.intValue() < 0;
        AbstractInt destPosPlusLength = destPosInt.add(lengthInt, IntegerType.JAVA_INT);
        cmpResult = destPosPlusLength.compareToApprox(destArrLength);
        final boolean destPosLTBound = cmpResult != null && cmpResult < 0;
        boolean needsIOOBExc = !(!srcPosLTZero && !destPosLTZero && !lengthLTZero && srcPosLTBound && destPosLTBound);
        return needsIOOBExc;
    }
}
