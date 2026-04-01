package aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations;

import java.util.*;

import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import immutables.*;

/**
 * Implementation of the a@{"name", ...} annotation ("a has cycles using
 * at least field 'name'").
 *
 * <h1>Semantics</h1>
 * <p>
 * This annotation is set whenever a reference can either be on a cycle,
 * or has (non-realized) successors which make up a cycle. It carries
 * some information to describe which fields <b>must</b> be used in such
 * a cycle.
 *
 * <h2>Inheritance</h2>
 * <p>
 *  Let a be an instance with a@{"field1"}. Then all newly-realized children
 *  of a are annotated with @{"field1"}.
 * </p>
 *
 * <h2>Effects</h2>
 * <p>
 *  When we resolve a possible equality, we check the resulting state for
 *  new cycles. If the references on a new cycle are not annotated with @,
 *  the refinement creates an unwanted successor, so we mark it as failed
 *  refinement and don't continue graph construction from it.
 * </p>
 * <p>
 *  If the references on the cycle are annotated with @{"field1", "field2",
 *  ...} we check that the cycle uses all of these fields. If not, we mark
 *  the refinement as failed and don't continue graph construction.
 * </p>
 *
 * @author Marc Brockschmidt
 */
class CyclicAnnotation implements Immutable {
    /**
     * Annotated reference.
     */
    final AbstractVariableReference ref;

    /**
     * Set of edges that need to exist on any cycle involving ref. May be
     * empty.
     */
    private final ImmutableSet<HeapEdge> neededEdges;

    /**
     * @param r Annotated reference.
     * @param neededE Set of edges that need to exist on any cycle involving
     *  ref.
     */
    CyclicAnnotation(final AbstractVariableReference r, final ImmutableSet<HeapEdge> neededE) {
        this.ref = r;
        assert (!neededE.contains(UnknownArrayMemberEdge.INSTANCE));
        this.neededEdges = neededE;
    }

    /**
     * @param r Annotated reference.
     * @param neededE Set of edges that need to exist on any cycle involving
     *  ref.
     */
    CyclicAnnotation(final AbstractVariableReference r, final Set<HeapEdge> neededE) {
        this(r, ImmutableCreator.create(neededE));
    }

    /**
     * @return Right hand side of the joins annotation;
     */
    public ImmutableSet<HeapEdge> getNeededEdges() {
        return this.neededEdges;
    }

    /**
     * Append a nice string representation to the string builder
     * @param sb a string builder
     */
    public void toString(final StringBuilder sb) {
        sb.append(this.ref).append("@").append(this.getNeededEdges());
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb);
        return sb.toString();
    }
}