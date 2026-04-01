package aprove.verification.oldframework.Bytecode.Utils;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Convenience class holding several routines needed in the refinement of
 * abstract arrays.
 *
 * @author Marc Brockschmidt
 */
public final class ArrayRefinement {
    /**
     * Private dummy constructor to prevent instantiation.
     */
    private ArrayRefinement() {
        assert (false) : "ArrayRefinement should never be instantiated";
    }

    /**
     * Performs an array realization refinement on the passed variable reference
     * to an abstract array if needed.
     * @param refToRefine variable reference to refine
     * @param curState state to work on
     * @param newStates list to push result state/edges in
     * @return true iff existence refinement was needed
     */
    public static boolean forArrayRealization(
        final AbstractVariableReference refToRefine,
        final State curState,
        final Collection<Pair<State, ? extends EdgeInformation>> newStates)
    {
        for (final AbstractVariableReference partnerRef : curState
            .getHeapAnnotations()
            .getEqualityGraph()
            .getPartners(refToRefine))
        {
            final boolean doneSomething =
                ObjectRefinement.forEquality(refToRefine, partnerRef, curState, newStates, true);
            // x =?= y for a NRIR is not removed
            assert (doneSomething || curState.getAllNRIRs().contains(partnerRef));

            if (doneSomething) {
                // yes, only do a single refinement here
                return true;
            }
        }
        final AbstractVariable var = curState.getAbstractVariable(refToRefine);
        if (var.isNULL()) {
            return false;
        }
        if (var instanceof Array) {
            return false;
        }
        /*
         * Okay, we need to refine. This only happens if the only explicit
         * information about the referenced instance is the outer instance of
         * java.lang.Object.
         */
        final State newState = curState.clone();

        // provide some abstract array length
        final AbstractInt aLength =
            AbstractInt.create(
                IntervalBound.ZERO,
                IntegerType.UNBOUND.getUpper(),
                IntervalBound.ZERO,
                IntegerType.UNBOUND.getUpper(),
                0,
                0);
        final AbstractVariableReference aLengthRef = newState.createReferenceAndAdd(aLength, OperandType.INTEGER);

        // create the array with this length
        final AbstractArray aA = new AbstractArray(aLengthRef);
        final AbstractVariableReference varRef = newState.createReferenceAndAdd(aA, OperandType.ARRAY);
        newState.replaceReference(refToRefine, varRef);

        final RefinementEdge edge = new RealizationRefinementEdge(refToRefine, varRef);
        edge.add(new JBCIntegerRelation(aLengthRef, IntegerRelationType.GE, 0));

        newStates.add(new Pair<State, EdgeInformation>(newState, edge));
        return true;
    }
}
