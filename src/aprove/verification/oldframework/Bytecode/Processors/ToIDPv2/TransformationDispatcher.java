package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Processors.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import immutables.*;

/**
 * This class facilitates value transformation by calling the different
 * value transformers. Furthermore, it keeps track of the set of already
 * transformed references.
 *
 * @author Christian von Essen
 */
public class TransformationDispatcher {

    /**
     * Transformer for integer values.
     */
    private static final IntegerTransformer INT_TRAFO = new IntegerTransformer();
    /**
     * Transformer for object instance values.
     */
    private static final InstanceTransformer INST_TRAFO = new InstanceTransformer();
    /**
     * Transformer for array values.
     */
    private static final ArrayTransformer ARRAY_TRAFO = new ArrayTransformer();

    /**
     * Information on which fields were used in the currently processed
     * SCC.
     */
    private final UsedFieldsAnalysis usedFieldAnalysis;

    /**
     * Convenience class holding arguments passed in from the strategy.
     */
    private final ConverterArguments arguments;

    /**
     * Create a fresh transformation dispatcher.
     *
     * @param annotations Holds annotations on the currently processed SCC
     *  of the graph, such as used instance fields.
     * @param args object holding parameters for the enclosing processor
     */
    public TransformationDispatcher(final SCCAnnotations annotations, final ConverterArguments args) {
        this.arguments = args;
        if (annotations.hasAnalysis(UsedFieldsAnalysis.class)) {
            this.usedFieldAnalysis = (UsedFieldsAnalysis) annotations.getAnalysis(UsedFieldsAnalysis.class);
        } else {
            this.usedFieldAnalysis = null;
        }
    }

    /**
     * @param <R> domain of the transformed value
     * @param state State in which <code>ref</code> and <code>oldRef</code> are
     *  used.
     * @param stateWithInformation Some other state from which information
     *  about some references should be retrieved
     * @param refMap Partial map of references from <code>state</code> to
     *  <code>stateWithInformation</code>. For refs that are mapped, the
     *  corresponding value from <code>stateWithInformation</code> is encoded.
     *  For all others, the value from <code>state</code> is taken.
     * @param oldRef Reference leading to the transformation of
     *  <code>ref</code>. May be null, implying that <code>ref</code> is at
     *  the root of a transformation (i.e. directly reachable from the state,
     *  through a local variable or operand stack).
     * @param ref Reference to transform
     * @param seenRefs References that were already transformed in this data
     *  structure. It's more or less the transitive closure of the oldRef
     *  relation, i.e. the oldRef in the transform() call for <code>oldRef
     *  </code>.
     * @param possiblePredecessors Set of references which possibly (but not
     *  always, i.e. using the annotation -+>) reach the changed reference.
     *  May be null, in which case it is assumed that no such reference exists.
     *  These references will be transformed into a fresh variable.
     * @param changedConnectionInformation an encoding of the heap connection
     *  that was changed in this evaluation (or null, if no such change exists).
     * @return The transformed term representing <code>ref</code>.
     */
    @SuppressWarnings({"unchecked", "rawtypes" })
    public <R extends SemiRing<R>> Collection<? extends ITerm<R>> transform(
        final State state,
        State stateWithInformation,
        Map<AbstractVariableReference, AbstractVariableReference> refMap,
        final AbstractVariableReference oldRef,
        final AbstractVariableReference ref,
        final Set<AbstractVariableReference> seenRefs,
        final Set<AbstractVariableReference> possiblePredecessors,
        final ReferenceAccessInformation changedConnectionInformation)
    {
        final Set<AbstractVariableReference> newSeenRefs = new LinkedHashSet<>(seenRefs);
        if (oldRef != null) {
            newSeenRefs.add(oldRef);
        }

        final Collection<? extends ITerm<R>> result;
        final State s;
        final AbstractVariableReference r;

        //If this reference is taken from the other state, continue working on that:
        if (refMap != null && refMap.containsKey(ref)) {
            s = stateWithInformation;
            r = refMap.get(ref);
            stateWithInformation = null;
            refMap = null;
        } else {
            s = state;
            r = ref;
        }

        if (newSeenRefs.contains(r) && !s.getHeapAnnotations().isMaybeExisting(r)) {
            result = (Collection) Collections.singleton((ITerm) InstanceTransformer.CYCLIC_INSTANCE_TERM);
        } else if (r.pointsToAnyIntegerType()) {
            result =
                (Collection) TransformationDispatcher.INT_TRAFO.transform(
                    s,
                    stateWithInformation,
                    refMap,
                    r,
                    this,
                    newSeenRefs,
                    possiblePredecessors,
                    changedConnectionInformation);
        } else if (r.pointsToInstance()) {
            result =
                (Collection) TransformationDispatcher.INST_TRAFO.transform(
                    s,
                    stateWithInformation,
                    refMap,
                    r,
                    this,
                    newSeenRefs,
                    possiblePredecessors,
                    changedConnectionInformation);
        } else if (r.pointsToArray()) {
            result =
                (Collection) TransformationDispatcher.ARRAY_TRAFO.transform(
                    s,
                    stateWithInformation,
                    refMap,
                    r,
                    this,
                    newSeenRefs,
                    possiblePredecessors,
                    changedConnectionInformation);
        } else {
            result = Collections.singleton(this.<R>getVariable(r, newSeenRefs, s));
        }
        return result;
    }

    /**
     * @param <R> domain of the transformed value
     * @param s State in which <code>ref</code> is used.
     * @param ref Reference to transform
     * @param possiblePredecessors Set of references which possibly (but not
     *  always, i.e. using the annotation -+>) reach the changed reference.
     *  May be null, in which case it is assumed that no such reference exists.
     *  These references will be transformed into a fresh variable.
     * @param changedConnectionInformation an encoding of the heap connection
     *  that was changed in this evaluation (or null, if no such change exists).
     * @return The transformed term representing <code>ref</code>.
     */
    public <R extends SemiRing<R>> Collection<? extends ITerm<R>> transform(
        final State s,
        final AbstractVariableReference ref,
        final Set<AbstractVariableReference> possiblePredecessors,
        final ReferenceAccessInformation changedConnectionInformation)
    {
        return this.<R>transform(
            s,
            null,
            null,
            null,
            ref,
            java.util.Collections.<AbstractVariableReference>emptySet(),
            possiblePredecessors,
            changedConnectionInformation);
    }

    /**
     * @param <R> domain of the transformed value
     * @param s State in which <code>ref</code> is used.
     * @param stateWithInformation Some other state from which information
     *  about some references should be retrieved
     * @param refMap Partial map of references from <code>state</code> to
     *  <code>stateWithInformation</code>. For refs that are mapped, the
     *  corresponding value from <code>stateWithInformation</code> is encoded.
     *  For all others, the value from <code>state</code> is taken.
     * @param ref Reference to transform
     * @param possiblePredecessors Set of references which possibly (but not
     *  always, i.e. using the annotation -+>) reach the changed reference.
     *  May be null, in which case it is assumed that no such reference exists.
     *  These references will be transformed into a fresh variable.
     * @param changedConnectionInformation an encoding of the heap connection
     *  that was changed in this evaluation (or null, if no such change exists).
     * @return The transformed term representing <code>ref</code>.
     */
    public <R extends SemiRing<R>> Collection<? extends ITerm<R>> transform(
        final State s,
        final State stateWithInformation,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap,
        final AbstractVariableReference ref,
        final Set<AbstractVariableReference> possiblePredecessors,
        final ReferenceAccessInformation changedConnectionInformation)
    {
        return this.<R>transform(
            s,
            stateWithInformation,
            refMap,
            null,
            ref,
            java.util.Collections.<AbstractVariableReference>emptySet(),
            possiblePredecessors,
            changedConnectionInformation);
    }

    /**
     * @param <R> domain of the transformed value
     * @param s State in which <code>ref</code> is used.
     * @param ref Reference to transform
     * @return The transformed term representing <code>ref</code>.
     */
    public <R extends SemiRing<R>> Collection<? extends ITerm<R>> transform(
        final State s,
        final AbstractVariableReference ref)
    {
        return this.<R>transform(
            s,
            null,
            null,
            null,
            ref,
            java.util.Collections.<AbstractVariableReference>emptySet(),
            null,
            null);
    }

    /**
     * @param s State in which <code>ref</code> is used.
     * @param ref Reference to transform
     * @return The transformed term representing <code>ref</code>.
     */
    public ITerm<BigInt> transformInt(final State s, final AbstractVariableReference ref) {
        assert (ref.pointsToAnyIntegerType());
        return TransformationDispatcher.INT_TRAFO
            .transform(s, null, null, ref, this, null, null, null)
            .iterator()
            .next();
    }

    /**
     * @param <R> ring of the variable
     * @param ref Reference to create variable from
     * @param seenRefs References that were already transformed in this data
     *  structure.
     * @param infix Some infix that is used in the variable name.
     * @param s State in which <code>ref</code> is used.
     * @param isPathLengthVar true iff the variable encodes a path length
     *  (implies an integer domain)
     * @return A Variable whose name is in some way deterministically related to
     * the given reference
     */
    @SuppressWarnings("unchecked")
    private <R extends SemiRing<R>> IVariable<R> getVariableWithInfix(
        final AbstractVariableReference ref,
        final Set<AbstractVariableReference> seenRefs,
        final String infix,
        final State s,
        final boolean isPathLengthVar)
    {
        final SemiRingDomain<?> varDomain;
        if (isPathLengthVar) {
            varDomain = DomainFactory.INTEGERS;
        } else {
            varDomain = ref.getSemiRingDomain();
        }
        if (s != null && this.isPossiblyCyclic(ref, s)) {
            return (IVariable<R>) ITerm.createVariable(ref + infix + TransformationDispatcher.cyclicPostfix(seenRefs), varDomain);
        } else {
            return (IVariable<R>) ITerm.createVariable(ref.toString() + infix, varDomain);
        }
    }

    /**
     * @param <R> ring of the variable
     * @param ref Reference to create variable from
     * @param seenRefs References that were already transformed in this data
     *  structure.
     * @param s State in which <code>ref</code> is used.
     * @return A Variable whose name is in some way deterministically related to
     * the given reference
     */
    public <R extends SemiRing<R>> IVariable<R> getVariable(
        final AbstractVariableReference ref,
        final Set<AbstractVariableReference> seenRefs,
        final State s)
    {
        return this.<R>getVariableWithInfix(ref, seenRefs, "", s, false);
    }

    /**
     * @param ref Reference to create variable from
     * @param seenRefs References that were already transformed in this data
     *  structure.
     * @param s State in which <code>ref</code> is used.
     * @return A Variable whose name is in some way deterministically related to
     * the given reference and has a name indicating that it should contain
     * array values.
     */
    public IVariable<UnknownRing> arrayVariable(
        final AbstractVariableReference ref,
        final Set<AbstractVariableReference> seenRefs,
        final State s)
    {
        return this.<UnknownRing>getVariableWithInfix(ref, seenRefs, "arr", s, false);
    }

    /**
     * @param ref Reference to transform
     * @param seenRefs References that were already transformed in this data
     *  structure.
     * @param s State in which <code>ref</code> is used.
     * @return A variable that should be used for transforming the not yet
     *  realized part of an instance
     */
    public IVariable<UnknownRing> nonRealizedSubInstanceVariable(
        final AbstractVariableReference ref,
        final Set<AbstractVariableReference> seenRefs,
        final State s)
    {
        return this.<UnknownRing>getVariableWithInfix(ref, seenRefs, "sub", s, false);
    }

    /**
     * @param ref Reference to Transform
     * @param seenRefs References that were already transformed in this data
     *  structure.
     * @param s State in which <code>ref</code> is used.
     * @return A variable that should be used for transforming a reference
     *  which might reach a changed reference (i.e. there is a change in
     *  the abstracted part of the heap which is visible from <code>ref</code>).
     */
    public ITerm<UnknownRing> changedByWriteAccessVariable(
        final AbstractVariableReference ref,
        final Set<AbstractVariableReference> seenRefs,
        final State s)
    {
        return this.getVariableWithInfix(ref, seenRefs, "put", s, false);
    }

    /**
     * @param ref Reference to create variable from
     * @param s State in which <code>ref</code> is used.
     * @return A Variable whose name is in some way deterministically related to
     * the given reference and indicates that it encodes the length.
     */
    public IVariable<BigInt> getVariableLength(final AbstractVariableReference ref, final State s) {
        return this.getVariableWithInfix(ref, Collections.<AbstractVariableReference>emptySet(), "_l", s, true);
    }

    /**
     * @param ref Reference to create variable from
     * @param s State in which <code>ref</code> is used.
     * @return A Variable whose name is in some way deterministically related to
     * the given reference and indicates that it encodes the array length.
     */
    public IVariable<BigInt> getVariableArrayLength(final AbstractVariableReference ref, final State s) {
        return this.getVariableWithInfix(ref, Collections.<AbstractVariableReference>emptySet(), "_al", s, true);
    }

    /**
     * @param ref Reference to create variable from
     * @param s State in which <code>ref</code> is used.
     * @return A Variable whose name is in some way deterministically related to
     * the given reference and indicates that it encodes the length.
     */
    public IVariable<BigInt> getVariableLengthChanged(final AbstractVariableReference ref, final State s) {
        return this.getVariableWithInfix(ref, Collections.<AbstractVariableReference>emptySet(), "_lC", s, true);
    }

    /**
     * @param ref Some reference
     * @param s Some state
     * @return true iff the reference <code>ref</code> can be part of a cyclic
     *  structure only involving edges that are read in the currently processed
     *  SCC.
     */
    private boolean isPossiblyCyclic(final AbstractVariableReference ref, final State s) {
        final CyclicStructures cyclics = s.getHeapAnnotations().getCyclicStructures();
        if (!cyclics.isCyclic(ref)) {
            return false;
        }
        if (this.usedFieldAnalysis != null) {
            final ImmutableSet<HeapEdge> neededEdges = cyclics.getNeededEdgesOf(ref);
            for (final HeapEdge edge : neededEdges) {
                if (edge instanceof InstanceFieldEdge) {
                    final InstanceFieldEdge iFEdge = (InstanceFieldEdge) edge;
                    if (!this.usedFieldAnalysis
                        .getUsedFieldNames(iFEdge.getClassName())
                        .contains(iFEdge.getFieldName()))
                    {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /**
     * @param seenRefs References that were already transformed in this data
     *  structure.
     * @return Postfix used for cyclic variables. Depends of <code>seenRefs</code>
     */
    private static String cyclicPostfix(final Set<AbstractVariableReference> seenRefs) {
        return "" + seenRefs.hashCode();
    }

    /**
     * @return the analysis providing information about used fields.
     */
    public UsedFieldsAnalysis getUsedFieldAnalysis() {
        return this.usedFieldAnalysis;
    }

    /**
     * @return the arguments of the enclosing converter.
     */
    public ConverterArguments getConverterArguments() {
        return this.arguments;
    }

    /**
     * @param dra some definite reaches
     * @param refMap
     * @param newSuffix if true, add the suffix "new"
     * @return some fitting variable
     */
    public static IVariable<BigInt> createDefiniteReachabilityVariable(
        final DefiniteReachabilityAnnotation dra,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap,
        final boolean newSuffix)
    {
        AbstractVariableReference leftVar = dra.getFrom();
        AbstractVariableReference rightVar = dra.getTo();
        final String fieldLabel = dra.getFields().toString();

        if (refMap != null) {
            if (refMap.containsKey(leftVar)) {
                leftVar = refMap.get(leftVar);
            }
            if (refMap.containsKey(rightVar)) {
                rightVar = refMap.get(rightVar);
            }
        }

        String newName = leftVar.toString() + fieldLabel + rightVar.toString();
        if (newSuffix) {
            newName = newName + "new";
        }
        final IVariable<BigInt> iVar = ITerm.createVariable(newName, DomainFactory.INTEGERS);

        return iVar;
    }
}
