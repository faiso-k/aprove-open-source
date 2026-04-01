package aprove.verification.dpframework.CSDPProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

@NoParams
public class QCSDPProblemToQDPProblemProcessor
        extends QCSDPProcessor {

    public QCSDPProblemToQDPProblemProcessor() {
    }

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem obl) {
        return true;
    }

    @Override
    public Result processQCSDP(QCSDPProblem problem, Abortion aborter)
            throws AbortionException {
        aborter.checkAbortion();

        ReplacementMap rm = problem.getReplacementMap();

        QDPProblem todo;
        Proof proof;
        if (rm.isUnrestricted()) {
            // for an unrestricted replacement map, we can keep Q and
            // minimality. also then this processor is complete
            todo = QDPProblem.create(problem.getDp(), problem.getRWithQ(),
                    problem.isMinimal());
            proof = new ConvertedToQDPProblemProof(true);
            return ResultFactory.proved(todo, YNMImplication.EQUIVALENT, proof);
        } else {
            // neither Q nor minimality can be kept in the general case
            QTRSProblem rWithQ = QTRSProblem.create(problem.getR());
            todo = QDPProblem.create(problem.getDp(), rWithQ, false);
            proof = new ConvertedToQDPProblemProof(false);
            return ResultFactory.proved(todo, YNMImplication.SOUND, proof);
        }
    }

    private class ConvertedToQDPProblemProof
            extends Proof.DefaultProof {
        private boolean unrestricted;

        public ConvertedToQDPProblemProof(boolean unrestricted) {
            this.unrestricted = unrestricted;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            if (this.unrestricted) {
                return o.export("Converted QCSDP Problem to QDP Problem ")
                        + o.cite(Citation.DA_EMMES)
                        + o.export(" keeping Q and possibly minimality.");
            } else {
                return o.export("Converted QCSDP Problem to QDP Problem ")
                        + o.cite(Citation.DA_EMMES)
                        + o.export(", but could not keep Q or minimality.");
            }
        }
    };

}
