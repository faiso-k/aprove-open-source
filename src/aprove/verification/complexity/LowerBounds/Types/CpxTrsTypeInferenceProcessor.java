package aprove.verification.complexity.LowerBounds.Types;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.LowerBounds.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.Rule;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Utility.*;


public class CpxTrsTypeInferenceProcessor extends ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return Options.certifier == Certifier.NONE
                && obl instanceof CpxRelTrsProblem
                && !((CpxRelTrsProblem)obl).getRewriteStrategy().contractsMultipleRedexes();
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) {
        Set<Rule> rules = new LinkedHashSet<>();
        assert obl instanceof CpxRelTrsProblem;
        CpxRelTrsProblem cpxTrs = (CpxRelTrsProblem) obl;
        for (aprove.verification.dpframework.BasicStructures.Rule r: cpxTrs.getR()) {
            rules.add(new Rule(r.getLeft(), r.getRight(), 1));
        }
        for (aprove.verification.dpframework.BasicStructures.Rule r: cpxTrs.getS()) {
            rules.add(new Rule(r.getLeft(), r.getRight(), 0));
        }
        TrsTypes types = TypeInference.infer(rules, cpxTrs.getSignature(), cpxTrs.getDefinedSymbols());
        LowerBoundsTrs trs = new LowerBoundsTrs(rules, types,
            cpxTrs.getRewriteStrategy() == RewriteStrategy.INNERMOST);
        RenamingCentral renamingCentral = new RenamingCentral(trs.getUsedNames());
        return ResultFactory.proved(new CpxTrsLowerBoundsProblem(trs, renamingCentral), BothBounds.create(), new TypeInferenceProof());
    }

    private class TypeInferenceProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Inferred types.");
        }
    }
}
