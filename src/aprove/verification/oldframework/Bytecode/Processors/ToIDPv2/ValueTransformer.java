package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * This class is the base class of all value transformers.
 * These transformers are responsible for transforming a reference from a state
 * into a term.
 *
 * @author Christian von Essen
 */
public abstract class ValueTransformer {
    /**
     * Transform the given reference into a term.
     *
     * @param s State in which <code>ref</code> is used.
     * @param stateWithInformation Some other state from which information
     *  about some references should be retrieved
     * @param refMap Partial map of references from <code>state</code> to
     *  <code>stateWithInformation</code>. For refs that are mapped, the
     *  corresponding value from <code>stateWithInformation</code> is encoded.
     *  For all others, the value from <code>state</code> is taken.
     * @param ref Reference to transform
     * @param dispatcher transformation dispatcher used to encode the used
     *  variables.
     * @param seenRefs References that were already transformed in this data
     *  structure.
     * @param possiblePredecessors Set of references which possibly (but not
     *  always, i.e. using the annotation -+>) reach the changed reference.
     *  May be null, in which case it is assumed that no such reference exists.
     *  These references will be transformed into a fresh variable.
     * @param changedConnectionInformation an encoding of the heap connection
     *  that was changed in this evaluation (or null, if no such change exists).
     * @return A collection of terms that represent the transformed term. It
     *  is required that dropping any but one of the resulting terms is
     *  correct.
     */
    public abstract Collection<? extends ITerm<?>> transform(final State s,
            final State stateWithInformation,
            final Map<AbstractVariableReference, AbstractVariableReference> refMap,
            final AbstractVariableReference ref,
            final TransformationDispatcher dispatcher,
            final Set<AbstractVariableReference> seenRefs,
            final Set<AbstractVariableReference> possiblePredecessors,
            final ReferenceAccessInformation changedConnectionInformation);
}
