package aprove.input.Programs.llvm.problems;

import java.util.Iterator;
import java.util.Set;

import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.Utility.Graph.*;


public class LLVMLassoGraph extends SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> {
    
    public LLVMLassoGraph(SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> scc) {
        super(scc.getNodes(), scc);
    }

    @Override
    public String toDOT() {
        return this.toDOT(true, LLVMDebuggingFlags.USE_HTML_DOT_LAYOUT);
    }

    @Override
    public String toDOT(boolean showNrs) {
        return this.toDOT(showNrs, LLVMDebuggingFlags.USE_HTML_DOT_LAYOUT);
    }
    
    public String toDOT(boolean showNrs, boolean useHTMLLayout) {
     // Transforms this TerminationGraph into <em>one</em> dotty file containing
        // one cluster for every methodgraph.
        StringBuilder t = new StringBuilder();
        t.append("digraph dp_graph {\n");
        t.append("graph [mindist=0.3,nodesep=0.20,concentrate=true,ranksep=0.5];\n");
        //The new tabular layout requires "plaintext" shapes to avoid doubled frames.
        if (useHTMLLayout) {
            t.append("node [shape=plaintext,fontsize=10];\n");
        } else {
            t.append("node [shape=rectangle,fontsize=10];\n");
        }
        t.append("edge [labeldistance=3,headclip=true,fontsize=8];\n");
        Iterator<Node<LLVMAbstractState>> i = this.getNodes().iterator();
        while (i.hasNext()) {
            Node<LLVMAbstractState> from = i.next();
            if (!this.contains(from)) {
                continue;
            }
            t.append(from.getNodeNumber());
            t.append(" [");
            if (from.getObject() != null) {
                if (useHTMLLayout) {
                    t.append("label=<\n");
                    /*
                     * We are only interested in the predecessor if it's unique and connected with an Evaluation
                     * or Refinement Edge.
                     */
                    Set<Node<LLVMAbstractState>> set = this.getIn(from);
                    assert set != null;
                    @SuppressWarnings("unchecked")
                    Node<LLVMAbstractState> predecessorNode =
                            this.getIn(from).size() == 1 ?
                            ((Node<LLVMAbstractState>) this.getIn(from).toArray()[0]) :
                                null;
                    LLVMAbstractState predecessorState = null;
                    if (
                        predecessorNode != null
                        && (
                                this.getEdgeObject(predecessorNode, from) instanceof LLVMEvaluationInformation
                            || this.getEdgeObject(predecessorNode, from) instanceof LLVMRefinementInformation
                            || this.getEdgeObject(predecessorNode, from) instanceof LLVMMethodSkipEdge
                        )
                    ) {
                        predecessorState = predecessorNode.getObject();
                    }
                    final int nodeNumer = showNrs ? from.getNodeNumber() : -1;
                    Boolean isUniqueFunctionStart = null;
                    t.append(
                        from.getObject().toDOTString(
                            true,
                            nodeNumer,
                            predecessorState,
                            "TODO",
                            false,
                            isUniqueFunctionStart
                        )
                    );
                    t.append(">, ");
                } else {
                    t.append("label=\"");
                    t.append((showNrs ? from.getNodeNumber() + ": " : ""));
                    t.append(this.getDOTNodeLabelText(SimpleGraph.DOT, from));
                    t.append("\", ");
                }
            }
            t.append(this.getDOTFormatForNodeLabels(SimpleGraph.DOT, from));
            t.append("];\n");
        }
        
        Iterator<Edge<LLVMEdgeInformation, LLVMAbstractState>> it = this.getEdges().iterator();
        while (it.hasNext()) {
            Edge<LLVMEdgeInformation, LLVMAbstractState> edge = it.next();
            LLVMEdgeInformation edgeInfo = edge.getObject();
            Node<LLVMAbstractState> from = edge.getStartNode();
            Node<LLVMAbstractState> to = edge.getEndNode();
            t.append(from.getNodeNumber());
            t.append(" -> ");
            t.append(to.getNodeNumber());
            t.append(" [color=");
            t.append(edgeInfo.getDotColor());
            t.append(", label=\"");
            t.append(edgeInfo.getDotLabel());
            t.append("\"];\n");
        }
        t.append("}\n");
        return t.toString();
    }
}
