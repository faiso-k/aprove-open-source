/*
 * Created on 23.03.2006
 */
package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPInstantiationProcessor.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * The forward instantiation processor as described in JAR05
 *
 * @author thiemann
 */
public class QDPForwardInstantiationProcessor extends QDPTransformationProcessor {

    @ParamsViaArgumentObject
    public QDPForwardInstantiationProcessor(final QDPTransformationProcessor.Arguments arguments) {
        super(QDPTransformation.ForwardInstantiation, arguments);
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return super.isQDPApplicable(qdp) && (qdp.QsupersetOfLhsR() || !qdp.getRwithQ().isCollapsing());
    }

    @Override
    protected AbortableIterator<Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>> getTransformedRules(final Node<Rule> s_to_t,
        final Graph<Rule, ?> gr,
        final QDPProblem qdp,
        final Abortion aborter) throws AbortionException {
        return new QDPTransformationProcessor.MaybeOneIterator<>(this.getTransformed(s_to_t, gr, qdp, aborter));
    }

    private Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>> getTransformed(final Node<Rule> s_to_t,
        final Graph<Rule, ?> gr,
        final QDPProblem qdp,
        final Abortion aborter) throws AbortionException {
        final Set<Rule> newRules = new LinkedHashSet<>();
        final Set<Pair<Rule, Rule>> resRules = new LinkedHashSet<>();
        final TRSFunctionApplication s = s_to_t.getObject().getLhsInStandardRepresentation();
        final TRSTerm t = s_to_t.getObject().getRhsInStandardRepresentation();
        for (final Node<Rule> u_to_v : gr.getOut(s_to_t)) {
            final TRSSubstitution mgu = qdp.getDependencyGraph().getConnectingStarSubstitution(s_to_t, u_to_v);
            if (Globals.useAssertions) {
                // Added by cotto, Term.applySubstitution does not want
                // sigma==null
                assert (mgu != null) :
                    "Offending nodes where no connecting substitution was found:\nFrom: "
                    + u_to_v + "\nTo: " + s_to_t + "\nQDP Problem:\n\n" + qdp.toExternString();
            }
            final TRSFunctionApplication sSigma = s.applySubstitution(mgu);

            if (sSigma.getStandardRenumbered().equals(s)) {
                // we have to insert s_to_t again
                return null;
            }

            final Rule generatedRule = Rule.create(sSigma, t.applySubstitution(mgu));
            final Rule newRule = qdp.getPair(generatedRule);
            newRules.add(newRule);
            resRules.add(new Pair<>(generatedRule, newRule));

        }

        final TransformationHeuristic heuristic = new InstantiationVariableHeuristic(s, newRules);
        final Triple<Position, Set<Rule>, Rule> triple = new Triple<>(null, null, null);
        if (qdp.getInnermost()) {
            triple.y = qdp.getDependencyGraph().getUsableRules(s_to_t.getObject());
        }

        return new Quadruple<>(heuristic, YNMImplication.EQUIVALENT, resRules, triple);

    }


}
