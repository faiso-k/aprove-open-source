/*
 * Created on 16.04.2005
 */
package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * The standard instantiation processor as described in JAR05
 *
 * @author thiemann
 */
public class QDPInstantiationProcessor extends QDPTransformationProcessor {

    @ParamsViaArgumentObject
    public QDPInstantiationProcessor(final QDPTransformationProcessor.Arguments arguments) {
        super(QDPTransformation.Instantiation, arguments);
    }

    @Override
    protected AbortableIterator<Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>> getTransformedRules(final Node<Rule> s_to_t,
        final Graph<Rule, ?> gr,
        final QDPProblem qdp,
        final Abortion aborter) throws AbortionException {
        return new QDPTransformationProcessor.MaybeOneIterator<Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>>>(
            this.getTransformed(s_to_t, gr, qdp, aborter));
    }

    private Quadruple<TransformationHeuristic, YNMImplication, Set<Pair<Rule, Rule>>, Triple<Position, Set<Rule>, Rule>> getTransformed(final Node<Rule> s_to_t,
        final Graph<Rule, ?> gr,
        final QDPProblem qdp,
        final Abortion aborter) throws AbortionException {
        final Set<Rule> newRules = new LinkedHashSet<>();
        final Set<Pair<Rule, Rule>> resRules = new LinkedHashSet<>();
        final TRSFunctionApplication s = s_to_t.getObject().getLhsInStandardRepresentation();
        final TRSTerm t = s_to_t.getObject().getRhsInStandardRepresentation();
        for (final Node<Rule> u_to_v : gr.getIn(s_to_t)) {
            final TRSSubstitution mgu = qdp.getDependencyGraph().getConnectingSubstitution(u_to_v, s_to_t);
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

        return new Quadruple<>(heuristic, YNMImplication.EQUIVALENT, resRules, null);


    }


    static class InstantiationVariableHeuristic implements TransformationHeuristic {

        private final TRSFunctionApplication s;
        private final Set<Rule> newRules;

        public InstantiationVariableHeuristic(final TRSFunctionApplication s, final Set<Rule> newRules) {
            this.newRules = newRules;
            this.s = s;
        }

        @Override
        public boolean safeTransformation() {
            // check whether all new pairs contains strictly less variables than the original pair.
            final int nrVars = this.s.getVariables().size();
            for (final Rule rule : this.newRules) {
                if (rule.getVariables().size() >= nrVars) {
                    return false;
                }
            }
            return true;
        }

    }



}
