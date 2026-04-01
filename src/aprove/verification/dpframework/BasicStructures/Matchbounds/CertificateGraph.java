package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * The certificate created during the RFC match bound technique to
 * proof termination of a SRS - a graph - is represented by this
 * class. It basically extends <code>Graph</code> but provides some
 * more format function for different output methods.
 *
 * @author <a href="mailto:chang@i2.informatik.rwth-aachen.de">Christian Hang</a>
 * @version $Id$
 */
public class CertificateGraph<X> extends MultiGraph<X, AnnotatedFunctionSymbol>
        implements HTML_Able, LaTeX_Able, PLAIN_Able {

    private static final long serialVersionUID = 1L;

    private Node<X> startNode;
    private Node<X> sharpSink;

    /**
     * Creates a new <code>CertificateGraph</code> instance.
     *
     */
    public CertificateGraph() {

        super();

    }

    @Override
    public String toLaTeX() {

        return "";

    }

    public void setStartNode(final Node<X> node) {

        this.startNode = node;

    }

    public void setSharpSink(final Node<X> node) {

        this.sharpSink = node;

    }

    /**
     * Formats the certificate for plain text output
     *
     * @return a plain text representation of this certificate graph
     */
    @Override
    public String toPLAIN() {

        final StringBuilder output = new StringBuilder();
        output.append("The certificate consists of the following enumerated nodes:\n");

        boolean first = true;
        for (final Node<X> node : this.getNodes()) {
            if (first) {
                first = false;
            } else {
                output.append(", ");
            }
            output.append(node.getNodeNumber());
        }

        if (this.startNode != null && this.sharpSink != null) {
            output.append("\n\nNode " + this.startNode.getNodeNumber() + " is start node and node " + this.sharpSink + " is final node.\n\n");
        }

        output.append("Those nodes are connected through the following edges:\n\n");

        for (final EdgeEquality<AnnotatedFunctionSymbol, X> edge : this.getEdges()) {
            output.append("* " + edge.getStartNode().getNodeNumber());
            output.append(" to " + edge.getEndNode().getNodeNumber());
            if (!edge.getObject().isEmpty()) {
                output.append(" labelled ");
                String out = "";
                for (final AnnotatedFunctionSymbol symbol : edge.getObject()) {
                    out += symbol.f + "(" + symbol.nr + "), ";
                }
                out = out.substring(0, out.length() - 2);
                output.append(out);
            }
        }

        output.append("\n");
        return output.toString();

    }

    /**
     * Implements the <code>toHTML</code>-method required by the
     * <code>HTML_Able</code> Interface
     *
     * @return a <code>String</code> representing this model in HTML
     */
    @Override
    public String toHTML() {

        final StringBuilder output = new StringBuilder();
        output.append("<p>The certificate consists of the following enumerated nodes:</p><p>");

        boolean first = true;
        for (final Node<X> node : this.getNodes()) {
            if (first) {
                first = false;
            } else {
                output.append(", ");
            }
            output.append(node.getNodeNumber());
        }

        if (this.startNode != null && this.sharpSink != null) {
            output.append("</p><p>Node " + this.startNode.getNodeNumber() + " is start node and node " + this.sharpSink + " is final node.</p>");
        }

        output.append("<p>Those nodes are connected through the following edges:</p><ul>");

        for (final EdgeEquality<AnnotatedFunctionSymbol, X> edge : this.getEdges()) {
            output.append("<li>" + edge.getStartNode().getNodeNumber());
            output.append(" to " + edge.getEndNode().getNodeNumber());
            if (!edge.getObject().isEmpty()) {
                output.append(" labelled ");
                String out = "";
                for (final AnnotatedFunctionSymbol symbol : edge.getObject()) {
                    out += symbol.f + "(" + symbol.nr + "), ";
                }
                out = out.substring(0, out.length() - 2);
                out += "</li>\n";
                output.append(out);
            }

        }

        output.append("</ul>");
        return output.toString();

    }

    public String toDOTMatchingInserted(final Set<MatchBound.MatchCollector> matches, final Set<? extends Set<Edge<X, AnnotatedFunctionSymbol>>> insertedPaths) {

        final Set<Edge<X,AnnotatedFunctionSymbol>> matchedEdges = new LinkedHashSet<Edge<X,AnnotatedFunctionSymbol>>();
        for (final MatchBound.MatchCollector collector : matches) {
            matchedEdges.addAll(collector.getPath());
        }

        final Set<Edge<X,AnnotatedFunctionSymbol>> insertedEdges = new LinkedHashSet<Edge<X,AnnotatedFunctionSymbol>>();
        for (final Set<Edge<X, AnnotatedFunctionSymbol>> path : insertedPaths) {
            insertedEdges.addAll(path);
        }

        final StringBuilder t = new StringBuilder();
        t.append("digraph dp_graph {\nnode [outthreshold=100, inthreshold=100];\n");
        for (final Node<X> from : this.getNodes()) {
            Set<EdgeEquality<AnnotatedFunctionSymbol, X>> out =
                this.getOutEdges(from);
            if (out == null) {
                out = new LinkedHashSet<EdgeEquality<AnnotatedFunctionSymbol, X>>();
            }
            t.append(from.getNodeNumber() + " [");
            if (from.getObject() != null) {
                t.append("label=\"" + this.getPrettyString(from.getObject()) + "\", ");
            }
            t.append("fontsize=16");
            t.append("];\n");

            for (final EdgeEquality<AnnotatedFunctionSymbol, X> edge : out) {
                // edges between the following nodes
                t.append(from.getNodeNumber() + " -> {");
                t.append(edge.getEndNode().getNodeNumber() + "} ");
                String label = "[label = \"";
                for (final AnnotatedFunctionSymbol sym : edge.getObject()) {
                    if (sym == null) {
                        label += "null, ";
                    } else {
                        label += this.getPrettyString(sym) + ", ";
                    }
                    if (matchedEdges.contains(edge)) {
                        label += ", color = red, fontcolor = red";
                    } else if (insertedEdges.contains(edge)) {
                        label += ", color = blue, fontcolor = blue";
                    }
                label = label.substring(0, label.length() - 2);
                label += "\"];\n";
                t.append(label);
                }
            }
        }

        return t.toString() + "}\n";

    }

}
