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

/**
 * Docu-guess (fuhs):
 * This processor implements Theorem 43 from the paper
 *
 * Florian Frohn and J&uuml;rgen Giesl
 * Analyzing Runtime Complexity via Innermost Runtime Complexity
 * In Proc. LPAR '17, EPiC Series in Computing 46, pages 249-268, 2017.
 *
 * For a RelTrs R/S, this processor may delete rewrite rules from R or S
 * that are not reachable in rewrite sequences from basic terms.
 */
public class CpxTrsNestedDefinedSymbolProcessor extends RuntimeComplexityRelTrsProcessor {

    @Override
    protected boolean isRuntimeComplexityRelTrsApplicable(RuntimeComplexityRelTrsProblem obl) {
        return Options.certifier == Certifier.NONE && !obl.isConstructorSystem();
    }

    @Override
    protected Result processRuntimeComplexityRelTrs(RuntimeComplexityRelTrsProblem cpxTrs, Abortion aborter) throws AbortionException {
        NestedDefinedSymbolComputation dac = new NestedDefinedSymbolComputation(cpxTrs);
        Set<Rule> newRules = dac.activeRules();
        if (newRules.size() == cpxTrs.getRules().size()) {
            return ResultFactory.unsuccessful();
        } else {
            Set<Rule> newR = intersection(cpxTrs.getR(), newRules);
            Set<Rule> newS = intersection(cpxTrs.getS(), newRules);
            RuntimeComplexityRelTrsProblem newObl = RuntimeComplexityRelTrsProblem.create(ImmutableCreator.create(newR),
                ImmutableCreator.create(newS), cpxTrs.getRewriteStrategy(), cpxTrs.STerminatesInnermost());
            // the processor is not sound for lower bounds, as it might turn defined symbols into constructors
            return ResultFactory.proved(newObl, UpperBound.create(), dac.getProof());
        }
    }

}
