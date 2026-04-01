/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Processors.GraphProcessors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Multithread.*;

public abstract class ItpfGraphProcessor extends AbstractGraphProcessor<Result, IDPProblem> {

    private final GenericItpfRule<?> itpfProc;
    protected final ApplicationMode applicationMode;

    protected ItpfGraphProcessor(final GenericItpfRule<?> itpfProc,
            final ApplicationMode applicationMode) {
        super("ItpfGraphProcessor");

        if (itpfProc == null) {
            throw new IllegalArgumentException("itpfProcessor must not be null");
        }
        this.itpfProc = itpfProc;
        this.applicationMode = applicationMode;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return this.itpfProc.isApplicable(idp);
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return mark == this && this.applicationMode == ApplicationMode.Multistep;
    }

    @Override
    protected Result processIDPProblem(final IDPProblem idp,
        final Abortion aborter) throws AbortionException {
        final IDependencyGraph graph = idp.getIdpGraph();
        final List<ExecData> workers =
            new ArrayList<ExecData>(graph.getEdges().size()
                + graph.getNodes().size());
        for (final Map.Entry<IEdge, Itpf> edgeCond : graph.getEdgeConditions().entrySet()) {
            if (!edgeCond.getValue().isTrue()) {
                workers.add(new ItpfEdgeExecutorData(idp, this.itpfProc, graph,
                    edgeCond.getKey(), edgeCond.getValue(), ImplicationType.SOUND, this.applicationMode));
            }
        }
        for (final Map.Entry<INode, Itpf> nodeCond : graph.getNodeConditions().entrySet()) {
            if (!nodeCond.getValue().isTrue()) {
                workers.add(new ItpfNodeExecutorData(idp, this.itpfProc, graph,
                    nodeCond.getKey(), nodeCond.getValue(), ImplicationType.SOUND, this.applicationMode));
            }
        }
        MultithreadedExecutor.execute(workers, aborter);

        final EdgeConditionMap newEdgeFormulas =
            new EdgeConditionMap(idp.getIdpGraph().getItpfFactory(), graph.getFreshVarGenerator());

        final Map<INode, Itpf> newNodeFormulas = new LinkedHashMap<INode, Itpf>();
        for (final ExecData data : workers) {
            if (data.hasChanges()) {
                if (data.isEdge()) {
                    final IEdge edge = ((ItpfEdgeExecutorData) data).getEdge();
                    newEdgeFormulas.putReplace(edge, data.getResult());
                } else if (data.isNode()) {
                    final INode node = ((ItpfNodeExecutorData) data).getNode();
                    newNodeFormulas.put(node, data.getResult());
                }
            }
        }

        if (newEdgeFormulas.isEmpty() && newNodeFormulas.isEmpty()) {
            return ResultFactory.unsuccessful();
        } else {

            final IDependencyGraph newGraph =
                idp.getIdpGraph().change(
                    newNodeFormulas,
                    newEdgeFormulas.getMap(),
                    null,
                    null,
                    null,
                    this.mark);

            final YNMImplication direction;
            if (this.itpfProc.isSound()) {
                if (this.itpfProc.isComplete()) {
                    direction = YNMImplication.EQUIVALENT;
                } else {
                    direction = YNMImplication.SOUND;
                }
            } else {
                if (this.itpfProc.isComplete()) {
                    direction = YNMImplication.COMPLETE;
                } else {
                    direction = YNMImplication.ANTIVALENT;
                }
            }
            return ResultFactory.proved(idp.change(newGraph),
                direction, new ItpfGraphProof());
        }
    }

    public class ItpfGraphProof extends DefaultProof {

        @Override
        public final String export(final Export_Util o, final VerbosityLevel level) {
            return "Applied rule " + ItpfGraphProcessor.this.itpfProc.export(o, VerbosityLevel.LOW);
        }

    }

    protected static abstract class ExecData extends ItpfExecutorData {

        public ExecData(final IDPProblem idp, final GenericItpfRule<?> rule,
                final Itpf formula, final ImplicationType executionRequirements, final ApplicationMode mode) {
            super(idp, rule, formula, executionRequirements, mode);
        }

        public boolean isEdge() {
            return false;
        }

        public boolean isNode() {
            return false;
        }

    }

    protected static class ItpfEdgeExecutorData extends ExecData {

        private final IEdge edge;

        public ItpfEdgeExecutorData(final IDPProblem idp,
                final GenericItpfRule<?> itpfRule, final IDependencyGraph graph,
                final IEdge edge, final Itpf condition,
                final ImplicationType executionRequirements,
                final ApplicationMode mode) {
            super(idp, itpfRule, condition, executionRequirements, mode);
            this.edge = edge;
        }

        public IEdge getEdge() {
            return this.edge;
        }

        @Override
        public boolean isEdge() {
            return true;
        }
    }

    protected static class ItpfNodeExecutorData extends ExecData {

        private final INode node;

        public ItpfNodeExecutorData(final IDPProblem idp,
                final GenericItpfRule<?> itpfRule, final IDependencyGraph graph,
                final INode node, final Itpf condition,
                final ImplicationType executionRequirements,
                final ApplicationMode mode) {
            super(idp, itpfRule, condition, executionRequirements, mode);
            this.node = node;
        }

        public INode getNode() {
            return this.node;
        }

        @Override
        public boolean isNode() {
            return true;
        }

    }

}
