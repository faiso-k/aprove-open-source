package aprove.verification.dpframework.CSDPProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public abstract class QCSDPTransformationProcessor
        extends QCSDPProcessor {

    abstract protected String getTransformationName();

    abstract protected Citation[] getCitations();

    /**
     *
     * @param problem
     * @param s_to_t
     *            in SECOND_STANDARD_PREFIX form
     * @param r
     *            in STANDARD_STANDARD_PREFIX form
     * @return
     */
    abstract protected TransformationInfo applyTransformation(
            QCSDPProblem problem, Rule s_to_t, GeneralizedTRS r);

    @Override
    protected Result processQCSDP(QCSDPProblem problem, Abortion aborter)
            throws AbortionException {

        ImmutableSet<Rule> pairs = problem.getDp();

        GeneralizedTRS r = GeneralizedTRS.create(problem
                .getRInPrefixForm(TRSTerm.STANDARD_PREFIX));

        for (Rule s_to_t : pairs) {
            aborter.checkAbortion();

            TransformationInfo info = this.applyTransformation(problem, s_to_t
                    .getWithRenumberedVariables(TRSTerm.SECOND_STANDARD_PREFIX), r);
            if (info == null) {
                continue;
            }

            ImmutableSet<Rule> newPairs = info.getRules();

            // very simple heuristic: if the new pairs contains the old one, we
            // have gained nothing, so...
            if (newPairs.contains(s_to_t)) {
                continue;
            }

            // at least for instantiation and forward instantiation at least one
            // pair must be returned. otherwise, the dp-graph approximation
            // would not be correct.
            assert (!newPairs.isEmpty());

            QCSDPProblem newProblem = QCSDPProblem.create(problem, s_to_t,
                    newPairs, info.mustReconnectRhs());

            if (this.transformationIsSafe(problem, newProblem)) {
                Proof proof = new TransformationProof(this, problem, s_to_t,
                        newPairs);
                return ResultFactory.proved(newProblem,
                        info.isComplete() ? YNMImplication.EQUIVALENT
                                : YNMImplication.SOUND, proof);
            }
        }

        return ResultFactory.unsuccessful();
    }

    private boolean transformationIsSafe(QCSDPProblem problem,
            QCSDPProblem newProblem) {
        // FIXME for now it is non-terminating in some cases...
        return true;
    }

    protected class TransformationProof extends DefaultProof {

        private final Rule transformedPair;

        private final ImmutableSet<Rule> newPairs;

        private final QCSDPTransformationProcessor proc;

        public TransformationProof(QCSDPTransformationProcessor proc,
                QCSDPProblem problem, Rule transformedPair,
                ImmutableSet<Rule> newPairs) {

            this.proc = proc;
            this.transformedPair = transformedPair;
            this.newPairs = newPairs;

            this.shortName = proc.getClass().getSimpleName();
            this.longName = proc.getTransformationName();
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();

            sb.append(o.export("Using the ")
                    + o.export(this.proc.getTransformationName())
                    + o.cite(this.proc.getCitations()) + o.export(" Processor")
                    + o.newline());
            sb.append(o.export("the pair "));
            sb.append(o.export(this.transformedPair) + o.newline());
            sb.append(o.export("was transformed to the following new pairs: "));
            sb.append(o.set(this.newPairs, Export_Util.RULES));
            sb.append(o.newline());

            return sb.toString();
        }

    }
}
