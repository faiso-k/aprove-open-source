package aprove.verification.oldframework.IntTRS.Ranking;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Tries to find a transition invariant.
 * If this is successful, then termination is shown.
 * @author Matthias Hoelzel
 */
public class RankingProcessor extends Processor.ProcessorSkeleton {
    /** Some arguments */
    private final Arguments arguments;

    /** Some arguments */
    public static class Arguments {
    }

    /**
     * A constructor.
     * @param args Arguments for the processor.
     */
    public RankingProcessor(final Arguments args) {
        this.arguments = args;
    }

    /**
     * A constructor without arguments.
     */
    public RankingProcessor() {
        this.arguments = new Arguments();
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSProblem problem;
        if (obl instanceof IRSProblem) {
            problem = (IRSProblem) obl;
        } else {
            problem = new IRSProblem((IRSwTProblem) obl);
        }
        final RankingProof proof = new RankingProof();

        final RankingWorker worker = new RankingWorker(problem, proof, aborter);

        final boolean result = worker.work();

        if (result) {
            return ResultFactory.proved(proof);
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me), Matthias Hoelzel
     */
    class RankingProof extends DefaultProof {
        /**
         * The transition invariant! If such a thing exists, then
         * termination is shown.
         */
        private TransitionInvariant transitionInvariant;

        /**
         * Creates the proof.
         * */
        public RankingProof() {
        }

        public void setTransitionInvariant(final TransitionInvariant ti) {
            this.transitionInvariant = ti;
        }

        /**
         * @param eu export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            if (this.transitionInvariant != null) {
                return this.transitionInvariant.export(eu);
            } else {
                return "";
            }
        }
    }
}
