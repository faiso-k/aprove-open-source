package aprove.verification.dpframework.Heuristics.Processors;

import aprove.input.Programs.prolog.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.TRSProblem.*;

@NoParams
public class WST06Heuristic extends Processor.ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        String stratName;
        if (obl instanceof QTRSProblem) {
            QTRSProblem qtrs = (QTRSProblem) obl;
            if (true || qtrs.getMaxArity() > 1) {
                stratName = "qtrs";
            } else {
                stratName = "qsrs";
            }
        } else if (obl instanceof TRS) {
            TRS trs = (TRS) obl;
            if (trs.getProgram().isMaxUnary()) {
                stratName = "srs";
            } else {
                stratName = "trs";
            }
        } else if (obl instanceof ETRSProblem) {
            stratName = "equ";
        } else if (obl instanceof HaskellProgram) {
            stratName = "hs";
        } else if (obl instanceof PrologProblem) {
            stratName = "npl";
        } else if (obl instanceof RelTRSProblem) {
            stratName = "rtrs";
        } else if (obl instanceof CSRProblem) {
            stratName = "csr";
        } else if (obl instanceof GTRSProblem) {
            stratName = "gtrs";
        } else if (obl instanceof CTRSProblem) {
            stratName = "ctrs";
        } else if (obl instanceof QDPProblem) {
            stratName = "qdp";
        } else {
            throw new RuntimeException("unknown input");
        }
        // add case for CTRS, RSRS
        return ResultFactory.justANewStrategy(new VariableStrategy(stratName).getExecutableStrategy(oblNode, rti));
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return true;
    }

}
