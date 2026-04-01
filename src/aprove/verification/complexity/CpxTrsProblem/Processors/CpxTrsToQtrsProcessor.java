package aprove.verification.complexity.CpxTrsProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

public class CpxTrsToQtrsProcessor extends RuntimeComplexityTrsProcessor {

    @Override
    protected boolean isRuntimeComplexityTrsApplicable(RuntimeComplexityTrsProblem obl) {
        return true;
    }

    @Override
    protected Result processRuntimeComplexityTrs(RuntimeComplexityTrsProblem cpxTrs, Abortion aborter)
            throws AbortionException {
        QTRSProblem qtrs = QTRSProblem.create(cpxTrs.getR());
        if (cpxTrs.getRewriteStrategy() != RewriteStrategy.FULL) {
            qtrs = qtrs.createInnermost();
        }
        TruthValue finite = ComplexityYNM.createUpper(ComplexityValue.finite());
        return ResultFactory.proved(qtrs, ComplexityIfTerminatingImplication.create(finite), new CpxTrsToQtrsProof());
    }

    private static class CpxTrsToQtrsProof extends CpxProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Proving termination on all terms instead of termination on constructor-based start terms");
        }

    }
}
