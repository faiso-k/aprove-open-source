package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Matthias Hoelzel
 *
 */
public class MCSShadow {
    public LinkedHashSet<GeneralizedRule> nodes;
    public LinkedHashSet<Triple<GeneralizedRule, Itpf, GeneralizedRule>> edges;

    /**
     * Constructor
     */
    public MCSShadow() {
        this.nodes = new LinkedHashSet<GeneralizedRule>();
        this.edges = new LinkedHashSet<Triple<GeneralizedRule, Itpf, GeneralizedRule>>();
    }

    @Override
    public String toString() {
        final StringBuilder result = new StringBuilder("MCSShadow {\nNodes:\n");
        for (final GeneralizedRule node : this.nodes) {
            result.append(node.toString());
            result.append('\n');
        }
        result.append("Edges:\n");
        for (final Triple<GeneralizedRule, Itpf, GeneralizedRule> edge : this.edges) {
            result.append(edge.toString());
            result.append('\n');
        }
        result.append("}\n");
        return result.toString();
    }
}
