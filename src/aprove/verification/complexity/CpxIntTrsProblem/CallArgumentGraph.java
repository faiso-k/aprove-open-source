package aprove.verification.complexity.CpxIntTrsProblem;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

@SuppressWarnings("serial")
public class CallArgumentGraph extends Graph<CallArgument, Void> {

    public String toDOT(ImmutableLinkedHashSet<FunctionSymbol> g, ImmutableLinkedHashMap<CallArgument,LocalComplexityValue> sizeBounds) {
        final StringBuilder t = new StringBuilder("digraph dp_graph {\n");

        t.append("subgraph cluster_key { style=filled; color=lightgrey; node [style=filled,color=white];"+
        "start [label=\"start node\", shape=octagon]; normal [label=\"normal node\", shape=box]; }");

        HTML_Util hu = new HTML_Util();

        final Iterator<Node<CallArgument>> i = this.getNodes().iterator();
        while (i.hasNext()) {
            final Node<CallArgument> from = i.next();
            Set<Node<CallArgument>> out = this.getOut(from);
            if (out == null) {
                out = new LinkedHashSet<>();
            }
            t.append(from.getNodeNumber() + " [");
            CallArgument alpha = from.getObject();
            boolean isStartNode = g.contains(alpha.rule.getRootSymbol());
            t.append(this.getNodeLabel(isStartNode, from, hu, sizeBounds.get(alpha)));
            t.append("fontsize=16];");
            final Iterator<Node<CallArgument>> j = out.iterator();
            if (!j.hasNext()) {
                continue;
            }
            t.append(from.getNodeNumber() + " -> {");
            while (j.hasNext()) {
                final Node<CallArgument> to = j.next();
                t.append(to.getNodeNumber() + " ");
            }
            t.append("};\n");
        }
        return t.toString() + "}\n";
    }

    private String getNodeLabel(boolean isStartNode, Node<CallArgument> from, HTML_Util hu, LocalComplexityValue globalComplexityValue) {
        CallArgument o = from.getObject();
        LocalSizeBound lsb = o.rule.getLocalSizeBound(o, AbortionFactory.create());
        return "label=<"
            + o.export(hu)
            + "<br/>"
            + "local: "
            + lsb.getC().export(hu)
            + ", global: "
            + globalComplexityValue.export(hu)
            + ">, shape=box, "
            + (isStartNode ? "shape=octagon, " : "");
    }
}
