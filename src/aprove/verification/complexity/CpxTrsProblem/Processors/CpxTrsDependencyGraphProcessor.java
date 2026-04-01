package aprove.verification.complexity.CpxTrsProblem.Processors;

import static aprove.verification.oldframework.Utility.Collection_Util.*;

import java.util.*;

import aprove.cli.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxRelTrsProblem.Processors.*;
import aprove.verification.complexity.CpxTrsProblem.Processors.Utility.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

public class CpxTrsDependencyGraphProcessor extends RuntimeComplexityRelTrsProcessor {

    @Override
    protected boolean isRuntimeComplexityRelTrsApplicable(RuntimeComplexityRelTrsProblem obl) {
        return Options.certifier == Certifier.NONE && !obl.isConstructorSystem();
    }

    @Override
    protected Result processRuntimeComplexityRelTrs(RuntimeComplexityRelTrsProblem cpxTrs, Abortion aborter) throws AbortionException {
        DependencyGraphComputation apc = new DependencyGraphComputation(cpxTrs);
        Set<Rule> newRules = apc.reachableRules();
        if (newRules.size() == cpxTrs.getRules().size()) {
            return ResultFactory.unsuccessful();
        } else {
            Set<Rule> newR = intersection(cpxTrs.getR(), newRules);
            Set<Rule> newS = intersection(cpxTrs.getS(), newRules);
            RuntimeComplexityRelTrsProblem newObl = RuntimeComplexityRelTrsProblem.create(ImmutableCreator.create(newR), ImmutableCreator.create(newS), cpxTrs.getRewriteStrategy(), cpxTrs.STerminatesInnermost());
            // the processor is not sound for lower bounds, as it might turn defined symbols into constructors
            return ResultFactory.proved(newObl, UpperBound.create(), apc.getProof());
        }
    }

}
