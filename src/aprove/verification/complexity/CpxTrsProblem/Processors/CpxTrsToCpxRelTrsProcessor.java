package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;


public class CpxTrsToCpxRelTrsProcessor extends RuntimeComplexityTrsProcessor {

    @Override
    protected boolean isRuntimeComplexityTrsApplicable(RuntimeComplexityTrsProblem obl) {
        return Options.certifier == Certifier.NONE;
    }

    @Override
    protected Result processRuntimeComplexityTrs(RuntimeComplexityTrsProblem cpxTrs, Abortion aborter) throws AbortionException {
        return ResultFactory.proved(RuntimeComplexityRelTrsProblem.create(cpxTrs.getR(),
            ImmutableCreator.create(Collections.emptySet()), cpxTrs.getRewriteStrategy(), true),
            BothBounds.create(), new CpxTrsToCpxRelTrsProof());
    }

    private class CpxTrsToCpxRelTrsProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Transformed TRS to relative TRS where S is empty.");
        }

    }
}
