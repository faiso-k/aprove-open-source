package aprove.verification.complexity.LowerBounds;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxRelTrsProblem.Processors.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;

public class CpxRelTrsToDecreasingLoopProblemProcessor extends CpxRelTrsProcessor {

    @Override
    protected Result processCpxRelTrs(CpxRelTrsProblem obl, Abortion aborter, RuntimeInformation rti) {
        BasicObligation newObl = DecreasingLoopProblem.initial(obl);
        return ResultFactory.proved(newObl, LowerBound.create(), new RelTrsToDecreasingLoopProblemProof());
    }

    @Override
    protected boolean isCpxRelTrsApplicable(CpxRelTrsProblem obl) {
        return Options.certifier.isNone() && ! obl.getRewriteStrategy().contractsMultipleRedexes();
    }

    public static class RelTrsToDecreasingLoopProblemProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Transformed a relative TRS into a decreasing-loop problem.";
        }

    }

}
