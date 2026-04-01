package aprove.verification.idpframework.Core.IDPGraph;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Represents an edge from one node to another node in the IDependencyGraph.
 * @author mpluecke
 * @version $Id$
 */
public final class IEdge extends IDPExportable.IDPExportableSkeleton implements Immutable, Exportable, IDPExportable, EdgeOrNode, EdgeOrTerm, BooleanPolyVarKeyable {

    public static IEdge create(final INode from,
        final IPosition fromPos,
        final INode to,
        final EdgeType type) {
        return new IEdge(from, fromPos, to, type);
    }

    /**
     * From node
     */
    public final INode from;

    /**
     * Position of the outgoing edge.
     */
    public final IPosition fromPos;

    /**
     * To node
     */
    public final INode to;

    /**
     * The edge type
     */
    public final EdgeType type;

    /**
     * Cashed hash
     */
    private final Integer hash;


    /**
     * @param from From node.
     * @param to To node.
     * @param type
     */
    IEdge(final INode from, final IPosition fromPos, final INode to, final EdgeType type) {
        this.from = from;
        this.fromPos = fromPos;
        this.to = to;
        this.type = type;
        final int prime = 31;
        this.hash =
            Integer.valueOf(from.hashCode() + to.hashCode() * prime
                + prime + fromPos.hashCode() * prime * prime
                + type.hashCode() * prime * prime * prime);
    }

    public IEdge subtractType(final EdgeType type) {
        return this.changeType(this.type.subtractType(type));
    }

    public IEdge changeType(final EdgeType type) {
        if (this.type == type) {
            return this;
        } else {
            return new IEdge(this.from, this.fromPos, this.to, type);
        }
    }

    @Override
    public String getBooleanPolyVarName() {
        final StringBuilder sb = new StringBuilder();
        sb.append(this.from.id);

        if (!this.fromPos.isEmptyPosition()) {
            sb.append("@");
            sb.append(this.fromPos.toString());
        }

        sb.append("_");
        sb.append(this.to.id);

        return sb.toString();
    }

    @Override
    public boolean equals(final Object o) {
        if (o == this) {
            return true;
        } else if (o instanceof IEdge) {
            final IEdge io = (IEdge) o;
            return io.from.equals(this.from) && io.fromPos.equals(this.fromPos)
                && io.to.equals(this.to) && io.type.equals(this.type);
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return this.hash;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel level) {
        this.from.export(sb, o, level);
        if (!this.fromPos.isEmptyPosition()) {
            sb.append("@");
            sb.append(this.fromPos.export(o));
        }

        sb.append(" ");
        sb.append(o.rightarrow());
        sb.append(o.sup(this.type.export(o)));
        sb.append(" ");
        this.to.export(sb, o, level);
    }




}