package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * Worker class used to convert method graphs in the TerminationGraph to
 * sets of IRules.
 */
public class MethodGraphToRuleSetConverter extends ToRuleSetConverter {
    /**
     * The method graph we should convert.
     */
    private final MethodGraph methodGraph;

    /**
     * @param abort aborter we are supposed to check for abortions.
     * @param mGraph some method graph
     * @param ruleCreator an instance handling the actual conversion to rules
     */
    public MethodGraphToRuleSetConverter(final Abortion abort,
            final MethodGraph mGraph,
            final RuleCreator ruleCreator) {
        super(abort, ruleCreator);
        this.methodGraph = mGraph;
    }

    /**
     * @return the method graph this worker is converting
     */
    public MethodGraph getMethodGraph() {
        return this.methodGraph;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result
                + ((this.methodGraph == null) ? 0 : this.methodGraph.hashCode());
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
        final MethodGraphToRuleSetConverter other = (MethodGraphToRuleSetConverter) obj;
        if (this.methodGraph == null) {
            if (other.methodGraph != null) {
                return false;
            }
        } else if (!this.methodGraph.equals(other.methodGraph)) {
            return false;
        }
        return true;
    }

    /** {@inheritDoc} */
    @Override
    public Collection<Edge> getEdges() {
        return this.methodGraph.getEdges();
    }
}
