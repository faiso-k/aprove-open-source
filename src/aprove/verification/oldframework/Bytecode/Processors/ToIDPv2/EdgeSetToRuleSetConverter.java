package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * Worker class used to convert sets of edges in the TerminationGraph to sets
 * of IRules.
 */
public class EdgeSetToRuleSetConverter extends ToRuleSetConverter {
    /**
     * The edges we should convert.
     */
    private final Set<Edge> edges;

    /**
     * @param abort aborter we are supposed to check for abortions.
     * @param es some edges in a termination graph.
     * @param ruleCreator an instance handling the actual conversion to rules
     */
    public EdgeSetToRuleSetConverter(final Abortion abort, final Set<Edge> es,
            final RuleCreator ruleCreator) {
        super(abort, ruleCreator);
        this.edges = es;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.edges == null) ? 0 : this.edges.hashCode());
        return result;
    }

    /** {@inheritDoc} */
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
        final EdgeSetToRuleSetConverter other = (EdgeSetToRuleSetConverter) obj;
        if (this.edges == null) {
            if (other.edges != null) {
                return false;
            }
        } else if (!this.edges.equals(other.edges)) {
            return false;
        }
        return true;
    }

    /** {@inheritDoc} */
    @Override
    public Collection<Edge> getEdges() {
        return this.edges;
    }
}
