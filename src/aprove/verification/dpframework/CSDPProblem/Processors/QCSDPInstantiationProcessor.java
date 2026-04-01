package aprove.verification.dpframework.CSDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class QCSDPInstantiationProcessor
        extends QCSDPTransformationProcessor {

    private final CapMuEstimation eCapMu;

    @ParamsViaArguments("eCapMu")
    public QCSDPInstantiationProcessor(CapMuEstimation eCapMu) {
        this.eCapMu = eCapMu;
    }

    @Override
    protected TransformationInfo applyTransformation(QCSDPProblem problem,
            Rule s_t, GeneralizedTRS r) {

        if (Globals.useAssertions) {
            assert(s_t.checkVariablePrefix(TRSTerm.SECOND_STANDARD_PREFIX));
            for (TermPair pair : r) {
                assert(pair.checkVariablePrefix(TRSTerm.STANDARD_PREFIX));
            }
        }

        Graph<Rule, Object> graph = problem.getGraph().getGraph();
        ReplacementMap mu = problem.getReplacementMap();
        QTermSet q = problem.getQ();

        Node<Rule> s_t_node = graph.getNodeFromObject(s_t);
        Set<Rule> newPairs = new LinkedHashSet<Rule>();
        for (Node<Rule> u_v_node : graph.getIn(s_t_node)) {
            Rule u_v = u_v_node.getObject().getWithRenumberedVariables(
                    TRSTerm.THIRD_STANDARD_PREFIX);

            TRSTerm cappedV = this.eCapMu.capMu(mu, q, r, problem.isInnermost(), u_v);

            TRSSubstitution delta = cappedV.getMGU(s_t.getLeft());
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

        return new TransformationInfo(true, false, ImmutableCreator.create(newPairs));
    }

    @Override
    protected String getTransformationName() {
        return "Context-Sensitive Instantiation";
    }

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem obl) {
        return true;
    }

    @Override
    protected Citation[] getCitations() {
        return new Citation[] { Citation.LPAR08, Citation.DA_EMMES };
    }
}
