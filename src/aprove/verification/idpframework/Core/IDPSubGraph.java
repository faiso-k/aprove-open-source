package aprove.verification.idpframework.Core;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class IDPSubGraph extends IDPExportable.IDPExportableSkeleton implements Immutable {

    private final ImmutableSet<IEdge> edges;

    public IDPSubGraph(final ImmutableSet<IEdge> edges) {
        this.edges = edges;
    }

    public ImmutableSet<IEdge> getEdges() {
        return this.edges;
    }

    public boolean containsAll(final IDPSubGraph other) {
        return this.edges.containsAll(other.getEdges());
    }

    public boolean isEmpty() {
        return this.edges.isEmpty();
    }

    public int size() {
        return this.edges.size();
    }

    public boolean containsEdge(final IEdge edge) {
        return this.edges.contains(edge);
    }

    public IDPSubGraph removeEdges(final Set<IEdge> intersection) {
        final LinkedHashSet<IEdge> newSubGraph = new LinkedHashSet<IEdge>(this.edges);
        newSubGraph.removeAll(intersection);
        return new IDPSubGraph(ImmutableCreator.create(newSubGraph));
    }

    @Override
    public int hashCode() {
        return this.edges.hashCode();
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final IDPSubGraph other = (IDPSubGraph) obj;
        return this.edges.equals(other.edges);
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        sb.append(eu.set(this.edges, Export_Util.NICE_SET));
    }



}
