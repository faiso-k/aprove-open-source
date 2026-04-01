package aprove.verification.dpframework.IDPProblem.Processors.itpfExecution;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class ItpfSchedulerEdgeExecutorData extends ItpfSchedulerExecutorData<ItpfSchedulerEdgeProof> {

    protected final IdpEdge edge;

    public ItpfSchedulerEdgeExecutorData(IDPProblem idp,
            ImmutableList<IItpfRule> rules,
            Map<IItpfRule, Set<IItpfRule>> ruleGrouping, IdpEdge edge,
            IItpfRule.ApplicationMode mode, Abortion aborter) {
        super(idp, rules, ruleGrouping, mode, aborter);
        this.edge = edge;
    }

    public IdpEdge getEdge() {
        return this.edge;
    }

    @Override
    protected ItpfSchedulerEdgeProof createInitialProof() {
        return new ItpfSchedulerEdgeProof(this.edge, this.ruleGrouping);
    }

    @Override
    protected Itpf getInitialFormula() {
        return this.edge.getItpf();
    }

    public Itpf getResult() {
        return this.result;
    }
}
