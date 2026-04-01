/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.cap.*;
import aprove.verification.dpframework.IDPProblem.Processors.itpfExecution.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.itpf.IItpfRule.*;
import aprove.verification.dpframework.IDPProblem.itpf.rules.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

public class ItpfSchedulerGraphProcessor extends AbstractGraphProcessor {

    public static final Integer MAIN_TYPE = Integer.valueOf(0);

    protected final ImmutableList<IItpfRule> itpfProcs;
    protected final ApplicationMode applicationMode;

    @ParamsViaArgumentObject
    public ItpfSchedulerGraphProcessor (Arguments arguments) {
        this(ImmutableCreator.create(Arrays.asList(arguments.rules)), arguments.mode);
    }

    protected ItpfSchedulerGraphProcessor(ImmutableList<IItpfRule> itpfProcs, IItpfRule.ApplicationMode applicationMode) {
        if (itpfProcs == null) {
            throw new IllegalArgumentException("itpfProcs must not be null");
        }
        this.itpfProcs = itpfProcs;
        this.applicationMode = applicationMode;
    }

    @Override
    public boolean isIDPApplicable(IDPProblem idp) {
        return true;
    }

    @Override
    protected Result processIDPProblem(IDPProblem idp, Abortion aborter)
            throws AbortionException {

        Map<IItpfRule, Set<IItpfRule>> ruleGroupings = new LinkedHashMap<IItpfRule, Set<IItpfRule>>();
        // TODO group rules

        List<ItpfSchedulerEdgeExecutorData> workers = new ArrayList<ItpfSchedulerEdgeExecutorData>(idp.getIdpGraph().getEdges().size());
        for (IdpEdge edge : idp.getIdpGraph().getEdges()) {
            workers.add(new ItpfSchedulerEdgeExecutorData(idp, this.itpfProcs, ruleGroupings, edge, this.applicationMode, aborter));
        }
        MultithreadedExecutor.execute(workers, aborter);

        List<ItpfSchedulerEdgeProof> edgeProofs = new ArrayList<ItpfSchedulerEdgeProof>(workers.size());

        Map<IdpEdge, Itpf> newFormulas = new LinkedHashMap<IdpEdge, Itpf>();
        for (ItpfSchedulerEdgeExecutorData worker : workers) {
            if (worker.getEdge().getItpf() != worker.getResult()) {
                newFormulas.put(worker.getEdge(), worker.getResult());
                edgeProofs.add(worker.getProof());
            }
        }

        if (newFormulas.isEmpty()) {
            return ResultFactory.unsuccessful();
        } else {
            return ResultFactory.proved(idp.change(idp.getIdpGraph().changeLabels(newFormulas, this), null, null, null, this), YNMImplication.EQUIVALENT,
                new ItpfSchedulerGraphProof(ImmutableCreator.create(edgeProofs), idp.getRuleAnalysis().getPreDefinedMap()));
        }
    }

    public static class Arguments {
        public IItpfRule[] rules = new IItpfRule[]{new ItpfSimplify(), new ItpfRootConstr(), new ItpfVarReduct(), new ItpfBoolOp(), new ItpfCap(IECap.Estimation.getEstimation(null)), new ItpfStepDetect(), new ItpfUnify()};
        public ApplicationMode mode = ApplicationMode.Multistep;
    }


    protected static class ItpfSchedulerGraphProof extends DefaultProof {
        protected final List<ItpfSchedulerEdgeProof> edgeProofs;
        protected final IDPPredefinedMap predefinedMap;

        public ItpfSchedulerGraphProof(ImmutableList<ItpfSchedulerEdgeProof> edgeProofs, IDPPredefinedMap predefinedMap) {
            this.edgeProofs = edgeProofs;
            this.predefinedMap = predefinedMap;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            for (ItpfSchedulerEdgeProof edgeProof : this.edgeProofs) {
                sb.append(edgeProof.export(o, this.predefinedMap, level));
                sb.append(o.linebreak());
            }
            return sb.toString();
        }


    }

}
