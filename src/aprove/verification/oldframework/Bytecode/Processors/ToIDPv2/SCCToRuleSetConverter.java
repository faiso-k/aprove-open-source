package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;

/**
 * Worker class used to convert SCCs in the TerminationGraph to sets of IRules.
 */
public class SCCToRuleSetConverter extends ToRuleSetConverter {
    /**
     * The SCC we should convert.
     */
    private final JBCGraph scc;

    /**
     * @param abort aborter we are supposed to check for abortions.
     * @param s some SCC in a termination graph.
     * @param ruleCreator an instance handling the actual conversion to rules
     */
    public SCCToRuleSetConverter(final Abortion abort, final JBCGraph s,
            final RuleCreator ruleCreator) {
        super(abort, ruleCreator);
        this.scc = s;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.scc == null) ? 0 : this.scc.hashCode());
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
        final SCCToRuleSetConverter other = (SCCToRuleSetConverter) obj;
        if (this.scc == null) {
            if (other.scc != null) {
                return false;
            }
        } else if (!this.scc.equals(other.scc)) {
            return false;
        }
        return true;
    }

    /** {@inheritDoc} */
    @Override
    public Collection<Edge> getEdges() {
        return this.scc.getEdges();
    }
}
