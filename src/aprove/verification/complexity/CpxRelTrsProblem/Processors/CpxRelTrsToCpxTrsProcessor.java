package aprove.verification.complexity.CpxRelTrsProblem.Processors;

import static aprove.verification.oldframework.Utility.Collection_Util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class CpxRelTrsToCpxTrsProcessor extends RuntimeComplexityRelTrsProcessor {

    class RelTrsToTrsProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "transformed relative TRS to TRS";
        }

    }

    @Override
    protected Result processRuntimeComplexityRelTrs(RuntimeComplexityRelTrsProblem trs, Abortion aborter) {
        ImmutableSet<Rule> rules = ImmutableCreator.create(union(trs.getR(), trs.getS()));
        BasicObligation newObl;
        if (trs.isDerivational()) {
            newObl = DerivationalComplexityTrsProblem.create(rules, trs.getRewriteStrategy());
        } else {
            newObl = RuntimeComplexityTrsProblem.create(rules, trs.getRewriteStrategy());
        }
        return ResultFactory.proved(newObl, UpperBound.create(), new RelTrsToTrsProof());
    }

    @Override
    protected boolean isRuntimeComplexityRelTrsApplicable(RuntimeComplexityRelTrsProblem obl) {
        return Options.certifier == Certifier.NONE;
    }

}
