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
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.itpfExecution.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.itpf.IItpfRule.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

public abstract class ItpfGraphProcessor extends AbstractInitialGraphProcessor {

    public static final Integer MAIN_TYPE = Integer.valueOf(0);

    private IItpfRule itpfProc;
    private ApplicationMode applicationMode;

    protected ItpfGraphProcessor(IItpfRule itpfProc, IItpfRule.ApplicationMode applicationMode) {
        if (itpfProc == null) {
            throw new IllegalArgumentException("itpfProcessor must not be null");
        }
        this.itpfProc = itpfProc;
        this.applicationMode = applicationMode;
    }

    @Override
    public boolean isIDPApplicable(IDPProblem idp) {
        return this.itpfProc.isApplicable(idp);
    }

    @Override
    protected Result processIDPProblem(IDPProblem idp, Abortion aborter)
            throws AbortionException {
        List<ItpfGraphExecutorData> workers = new ArrayList<ItpfGraphExecutorData>(idp.getIdpGraph().getEdges().size());
        for (IdpEdge edge : idp.getIdpGraph().getEdges()) {
            workers.add(new ItpfGraphExecutorData(idp, this.itpfProc, edge, this.applicationMode));
        }
        MultithreadedExecutor.execute(workers, aborter);

        Map<IdpEdge, Itpf> newFormulas = new LinkedHashMap<IdpEdge, Itpf>();
        for (ItpfGraphExecutorData data : workers) {
            if (data.getEdge().getItpf() != data.getResult()) {
                newFormulas.put(data.getEdge(), data.getResult());
            }
        }

        if (newFormulas.isEmpty()) {
            return ResultFactory.unsuccessful();
        } else {
            return ResultFactory.proved(idp.change(idp.getIdpGraph().changeLabels(newFormulas, this), null, null, null, this), YNMImplication.EQUIVALENT,
                new ItpfGraphProof());
        }
    }

    public class ItpfGraphProof extends DefaultProof {
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Applied rule " + ItpfGraphProcessor.this.itpfProc.getDescription(NameLength.SHORT);
        }
    }

    @Override
    public IIDependencyGraph createInitialGraph(IDPRuleAnalysis ruleAnalysis, Abortion aborter) throws AbortionException {
        if (!(this.itpfProc instanceof IInitialItpfRule)) {
            throw new UnsupportedOperationException("Need initial ItpfRule.");
        }
        Triple<Set<Node>, Integer, Set<TRSVariable>> createNodes = AbstractInitialGraphProcessor.createInitialNodes(ruleAnalysis, aborter);
        Set<Node> nodes = createNodes.x;
        IInitialItpfRule itpf = (IInitialItpfRule) this.itpfProc;
        Set<IdpEdge> edges = new LinkedHashSet<IdpEdge>();
        for (Node n1 : nodes) {
            for (Node n2 : nodes) {
                Set<TRSTerm> S = new LinkedHashSet<TRSTerm>();
                Itpf formula;
                if (n1 == n2) {
                    S.add(n1.rule.getLeft());
                    TRSTerm n2LeftRenamed = n2.rule.getLeft().applySubstitution(TRSSubstitution.create(n1.loopSubstitution, true));
                    S.add(n2LeftRenamed);
                    S.addAll(n1.rule.getUnboundedVariables());
                    formula = itpf.processInitial(ruleAnalysis, ItpfItp.create(n1.rule.getRight(), ItpRelation.TO_TRANS, n2LeftRenamed, ImmutableCreator.create(S)), aborter);
                } else {
                    S.add(n1.rule.getLeft());
                    S.add(n2.rule.getLeft());
                    S.addAll(n1.rule.getUnboundedVariables());
                    S.addAll(n2.rule.getUnboundedVariables());
                    formula = itpf.processInitial(ruleAnalysis, ItpfItp.create(n1.rule.getRight(), ItpRelation.TO_TRANS, n2.rule.getLeft(), ImmutableCreator.create(S)), aborter);
                }
                formula = formula.normalize();
                if (!formula.isFalse()) {
                    edges.add(IdpEdge.create(
                            n1, n2,
                            formula,
                            this));
                }
            }
        }
        return IDependencyGraph.create(ruleAnalysis.getPAnalysis(), ImmutableCreator.create(nodes),
                ImmutableCreator.create(edges), YNM.MAYBE, createNodes.y, ImmutableCreator.create(createNodes.z), this);
    }


    protected static class ItpfGraphExecutorData extends ItpfExecutorData {

        private IdpEdge edge;

        public ItpfGraphExecutorData(IDPProblem idp, IItpfRule rule, IdpEdge edge, IItpfRule.ApplicationMode mode) {
            super(idp, rule, edge.getItpf(), mode);
            this.edge = edge;
        }

        public IdpEdge getEdge() {
            return this.edge;
        }
    }

}
