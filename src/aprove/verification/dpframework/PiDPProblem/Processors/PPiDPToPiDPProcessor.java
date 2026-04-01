package aprove.verification.dpframework.PiDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PiDPProblem.*;
import aprove.verification.dpframework.PiDPProblem.AfsRefinementAlgorithm.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class PPiDPToPiDPProcessor extends PiDPProblemProcessor {

    private final Heuristic heuristic;

    public enum Heuristic {
        ITB
    };

    public PPiDPToPiDPProcessor() {
        this(new Arguments());
    }

    @ParamsViaArgumentObject
    public PPiDPToPiDPProcessor(Arguments arguments) {
        this.heuristic = arguments.heuristic;
    }

    public static class Arguments {
        public PPiDPToPiDPProcessor.Heuristic heuristic =
            PPiDPToPiDPProcessor.Heuristic.ITB;
    }

    @Override
    public boolean isPiDPApplicable(AbstractPiDPProblem apidp) {
        return apidp instanceof PPiDPProblem;
    }

    @Override
    protected Result processPiDPProblem(AbstractPiDPProblem apidp,
        Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert (this.isApplicable(apidp));
        }
        PPiDPProblem ppidp = (PPiDPProblem) apidp;

        Afs Pi = ppidp.getPi();
        Set<GeneralizedRule> P = ppidp.getP();
        Set<GeneralizedRule> R = ppidp.getR();
        RefinementHeuristic heuristic = null;
        switch (this.heuristic) {
        case ITB:
            heuristic =
                new ImprovedTypeBasedRefinementHeuristic(new TypeGraph(R));
            break;
        }
        Pi = AfsRefinementAlgorithm.refineArgumentFilter(Pi, P, R, heuristic);
        PiDPProblem pidp =
            PiDPProblem.create(ImmutableCreator.create(P), PiTRSProblem.create(
                ImmutableCreator.create(R), new ImmutableAfs(Pi)));

        Proof proof = new PPiDPToPiDPProof();
        return ResultFactory.proved(pidp, YNMImplication.SOUND, proof);
    }

    private static class PPiDPToPiDPProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "";
        }

    }
}
