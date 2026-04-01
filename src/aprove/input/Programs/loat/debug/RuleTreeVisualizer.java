package aprove.input.Programs.loat.debug;

import java.util.*;

import aprove.input.Programs.loat.LoATOutputParser.*;

public class RuleTreeVisualizer {
    
    public static void toDOT(Node root) {
        StringBuilder labels = new StringBuilder();
        StringBuilder edges = new StringBuilder();
        
        List<Node> nodes = new ArrayList<>();
        nodes.add(root);
        while (!nodes.isEmpty()) {
            List<Node> nextNodes = new ArrayList<>();
            for (Node n : nodes) {
                labels.append(n.rule.getRuleNumber()+" [label=\""+n.toShortString()+"\"");
                
                if (n.node2 != null) {
                    labels.append(",style=filled, fillcolor=lightblue");
                } else if (n.node1 != null) {
                    labels.append(",style=filled, fillcolor=darkorchid");
                } else {
                    labels.append(",style=filled, fillcolor=darkseagreen");
                }
                labels.append("];\n");
                
                if (n.node1 != null) {
                    nextNodes.add(n.node1);
                    edges.append(n.rule.getRuleNumber()+" -> "+n.node1.rule.getRuleNumber()+" [];\n");
                }
                if (n.node2 != null) {
                    nextNodes.add(n.node2);
                    edges.append(n.rule.getRuleNumber()+" -> "+n.node2.rule.getRuleNumber()+" [];\n");
                }
            };
            nodes = nextNodes;
        }
        
        String str =  "digraph dp_graph {\n" + 
                "graph [mindist=0.3,nodesep=0.20,concentrate=true,ranksep=0.1];\n" + 
                "node [shape=rectangle,fontsize=10];\n" + 
                "edge [labeldistance=3,headclip=true,fontsize=8];\n" +
                labels.toString() +
                edges.toString() +
                "}";  
        FileWriter.dumpString(str, "ruleTree.dot");
    }
    
}