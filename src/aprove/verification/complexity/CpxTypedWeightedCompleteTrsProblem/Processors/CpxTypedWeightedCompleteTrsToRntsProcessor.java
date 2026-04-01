package aprove.verification.complexity.CpxTypedWeightedCompleteTrsProblem.Processors;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.CpxTypedWeightedCompleteTrsProblem.*;
import aprove.verification.complexity.CpxTypedWeightedTrsProblem.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Transforms a (partially) completely defined, typed, weighted TRS into
 * a RNTS (Recursive Natural Transition System) for upper bound irc analysis.
 * The transformation is done by applying size abstraction to all rules.
 *
 * Note that this is only applicable for innermost complexity,
 * as RNTS semantics are innermost.
 *
 * @author mnaaf
 */
public class CpxTypedWeightedCompleteTrsToRntsProcessor extends CpxTypedWeightedCompleteTrsProcessor {

    @Override
    protected boolean isCpxTypedWeightedCompleteTrsApplicable(CpxTypedWeightedCompleteTrsProblem obl) {
        CpxTypedWeightedTrsProblem cpxTrs = obl.getTypedWeightedTrs();
        if (!cpxTrs.isInnermost()) {
            return false;
        }
        if (!cpxTrs.isConstructorSystem()) {
            return false;
        }
        return true;
    }

    @Override
    protected Result processCpxTypedWeightedCompleteTrs(CpxTypedWeightedCompleteTrsProblem completeTrs, Abortion aborter) throws AbortionException {
        CpxTypedWeightedTrsProblem cpxTrs = completeTrs.getTypedWeightedTrs();

        FreshNameGenerator fng = new FreshNameGenerator(CollectionUtils.getNames(cpxTrs.getVariables()), FreshNameGenerator.VARIABLES);
        List<String> argNames = new ArrayList<>();
        Set<RntsRule> newRules = new LinkedHashSet<RntsRule>();

        for (WeightedRule rule : cpxTrs.getRules()) {
            newRules.add(SizeAbstraction.abstractRule(rule.getRule(), SimplePolynomial.create(rule.getWeight()), argNames, fng, cpxTrs)); //modifies argNames
        }

        CpxRntsProblem res = CpxRntsProblem.create(ImmutableCreator.create(newRules),cpxTrs,completeTrs.allowsPartialDerivations());
        return ResultFactory.proved(res, UpperBound.create(), new CpxTypedWeightedTrsToRntsProof(cpxTrs));
    }

    private static class CpxTypedWeightedTrsToRntsProof extends CpxProof {
        CpxTypedWeightedTrsProblem trs;

        public CpxTypedWeightedTrsToRntsProof(CpxTypedWeightedTrsProblem t) {
            this.trs = t;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append(o.escape("Transformed the TRS into an over-approximating RNTS by (improved) Size Abstraction.") + o.cond_linebreak());
            s.append(o.escape("The constant constructors are abstracted as follows:"));

            List<String> listing = new ArrayList<>();
            for (FunctionSymbol ctor : this.trs.getConstantConstructors()) {
                TRSTerm size = SizeAbstraction.abstractSize(TRSTerm.createFunctionApplication(ctor), this.trs);
                listing.add(ctor.export(o) + o.escape(" => ") + size.export(o));
            }

            s.append(o.linebreak());
            s.append(o.set(listing, Export_Util.RULES));
            return s.toString();
        }

    }
}
