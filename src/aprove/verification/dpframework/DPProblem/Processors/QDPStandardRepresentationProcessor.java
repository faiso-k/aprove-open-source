package aprove.verification.dpframework.DPProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import immutables.*;

/**
 * Rename rules to standard representation.
 * Primarily meant for exporting purposes, efficiency might be
 * improved by not disregarding cached components of the QDP.
 *
 * Note that in general this processor is not complete, but only
 * sound. It may introduce edges into the dependency graph
 * that have been deleted before, which can render a non-infinite
 * DP problem infinite.
 *
 * Example:
 * R = Q = {}; P = { C -> C }, but the DP graph has no edges.
 *
 * Then obviously there is no infinite path in the DP graph
 * and R is terminating, so the problem is not infinite.
 * But recomputing the DP graph from scratch will yield an
 * infinite problem with a self-loop in the DP graph at the
 * node (C -> C).
 *
 * Since this processor (for now) has the sole purpose of providing
 * human-readable export of QDP problems that have been generated
 * by transformations from programming languages, never claiming
 * equivalence is currently not an issue.
 *
 * @author fuhs
 */
public class QDPStandardRepresentationProcessor extends QDPProblemProcessor {

    private static final QDPStandardRepresentationProof theProof =
        new QDPStandardRepresentationProof();

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return true;
    }

    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter) throws AbortionException {
        QTRSProblem oldQtrs = qdp.getRwithQ();

        QTRSStandardRepresentationProcessor trsProc =
            new QTRSStandardRepresentationProcessor();
        QTRSProblem newQtrs = trsProc.computeStandardRepresentation(oldQtrs, aborter);
        ImmutableSet<Rule> oldP = qdp.getP();
        ImmutableSet<Rule> newP = trsProc.computeStandardRepresentation(oldP, aborter);

        if (newP == null) {
            if (newQtrs == null) {
                return ResultFactory.unsuccessful("This QDP Problem already is in standard representation.");
            }
            else {
                newQtrs = oldQtrs;
                newP = oldP;
            }
        }
        else if (newQtrs == null) {
            newQtrs = oldQtrs;
        }

        QDPProblem newQdp = QDPProblem.create(newP, newQtrs, qdp.getMinimal());

        // feel free to improve this code by figuring out the cases
        // where this "transformation" is equivalent (i.e., where there
        // are no "significant" changes to the dependency graph)
        return ResultFactory.proved(newQdp, YNMImplication.SOUND, QDPStandardRepresentationProcessor.theProof);
    }

    private static class QDPStandardRepresentationProof extends Proof {

        private QDPStandardRepresentationProof() {}

        @Override
        public String export(Export_Util o) {
            return "Renamed variables in rules of P and R to standard representation and built dependency graph anew.";
        }
    }
}
