package aprove.verification.idpframework.Core.IDPGraph;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Represents a node in the IDependencyGraph.
 * @author mpluecke
 * @version $Id$
 */
public class INode implements Immutable, Exportable, XmlExportable, IDPExportable, EdgeOrNode, NodeOrTerm, BooleanPolyVarKeyable {

    public static ImmutableSet<INode> EMPTY_SET = ImmutableCreator.create(Collections.<INode>emptySet());

    public static ImmutableSet<ImmutablePair<INode, ImmutableTermSubstitution>> EMPTY_SET_WITH_SUBSTITUTION = ImmutableCreator.create(Collections.<ImmutablePair<INode, ImmutableTermSubstitution>>emptySet());

    public static INode create(final int id) {
        return new INode(id);
    }

    /**
     * Id of the node for export.
     */
    public final int id;

    /**
     * @param id The id of this node (must be unique in the graph).
     */
    INode(final int id) {
        this.id = id;
    }

    @Override
    public int hashCode() {
        return 31 * this.id;
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
        final INode other = (INode) obj;
        return other.id == this.id;
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String getBooleanPolyVarName() {
        return "|" + this.id + "|";
    }

    @Override
    public final String export(final Export_Util o) {
        return this.export(o, IDPExportable.DEFAULT_LEVEL);
    }

    @Override
    public final String export(final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final StringBuilder sb = new StringBuilder();
        this.export(sb, o, verbosityLevel);
        return sb.toString();
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o, final VerbosityLevel verbosityLevel) {
        sb.append(o.escape("|"));
        sb.append(this.id);
        sb.append(o.escape("|"));
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        final Map<String, String> m = new HashMap<String, String>();
        m.put("id", Integer.toString(this.id));
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        return null;
    }
}
