package aprove.verification.dpframework.CSDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class QCSDPForwardInstantiationProcessor
        extends QCSDPTransformationProcessor {

    private static final Set<TRSTerm> emptyS =
        ImmutableCreator.create(java.util.Collections.<TRSTerm>emptySet());

    private static final QTermSet emptyQ = new QTermSet(
            new ArrayList<TRSFunctionApplication>());

    private final CapMuEstimation eCapMu;

    @ParamsViaArguments("eCapMu")
    public QCSDPForwardInstantiationProcessor(CapMuEstimation eCapMu) {
        this.eCapMu = eCapMu;
    }

    @Override
    protected TransformationInfo applyTransformation(QCSDPProblem problem,
            Rule s_t, GeneralizedTRS r) {

        if (Globals.useAssertions) {
            assert (s_t.checkVariablePrefix(TRSTerm.SECOND_STANDARD_PREFIX));

            for (TermPair pair : r) {
                assert (pair.checkVariablePrefix(TRSTerm.STANDARD_PREFIX));
            }
        }

        QCSUsableRules ur = problem.getQCSUsableRules();
        Graph<Rule, Object> graph = problem.getGraph().getGraph();
        ReplacementMap mu = problem.getReplacementMap();
        QTermSet q = problem.getQ();

        // build R'
        // no need to add u to s, since the mgu clears this up later
        Set<Rule> usable = ur.estimatedCSUsableRules(s_t);

        // reverse usable rules
        Set<TermPair> reversed = new LinkedHashSet<TermPair>();
        for (Rule rule : usable) {
            reversed.add(TermPair.create(rule.getRight(), rule.getLeft()));
        }

        GeneralizedTRS rPrime = GeneralizedTRS.create(ImmutableCreator
                .create(reversed));

        Node<Rule> s_t_node = graph.getNodeFromObject(s_t);
        Set<Rule> newPairs = new LinkedHashSet<Rule>();
        for (Node<Rule> u_v_node : graph.getOut(s_t_node)) {
            Rule u_v = u_v_node.getObject().getWithRenumberedVariables(
                    TRSTerm.THIRD_STANDARD_PREFIX);

            TRSTerm cappedU = this.eCapMu.capMu(mu, QCSDPForwardInstantiationProcessor.emptyQ, rPrime, false, QCSDPForwardInstantiationProcessor.emptyS, u_v
                    .getLeft());

            TRSSubstitution delta = cappedU.getMGU(s_t.getRight());
            if (delta == null) {
                continue;
            }

            Rule s_t_delta = Rule.create(
                    s_t.getLeft().applySubstitution(delta), s_t.getRight()
                            .applySubstitution(delta));

            TRSFunctionApplication u_delta = u_v.getLeft()
                    .applySubstitution(delta);

            if (!mu.inQMuNormalForm(q, s_t_delta.getLeft())) {
                continue;
            }

            if (!mu.inQMuNormalForm(q, u_delta)) {
                continue;
            }

            // delta seems to be a correct substitution
            newPairs.add(s_t_delta);
        }

        return new TransformationInfo(true, false, ImmutableCreator
                .create(newPairs));
    }

    @Override
    protected String getTransformationName() {
        return "Context-Sensitive Forward Instantiation";
    }

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem obl) {
        return true;
    }

    @Override
    protected Citation[] getCitations() {
        return new Citation[] { Citation.DA_EMMES };
    }
}
