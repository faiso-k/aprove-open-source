package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxITrsProblem.Processors.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfManager.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Converts a CpxIntTrs to a CpxRelTrs problem.
 * Here predefined functions are implemented via recursive rules
 * whose complexity is not supposed to be counted.
 *
 * Analogous to IDPtoQDPProcessor, but for complexity problems.
 *
 * We currently require that variables in the rhs and in the
 * constraint of a rule must also occur in its lhs.
 *
 * TODO Allow filtering away variables which occur in the rhs
 * but not in the lhs. Sound for upper bounds in complexity?
 *
 * @author Carsten Fuhs
 */
public class CpxIntTrsToCpxRelTrsProcessor extends CpxIntTrsProcessor {

    private static Logger log = Logger.getLogger(CpxITrsProcessor.class.getCanonicalName());

    /**
     * What is the highest absolute value of an integer literal allowed for
     * explicit conversion?
     */
    private final int limit;

    @ParamsViaArgumentObject
    public CpxIntTrsToCpxRelTrsProcessor(Arguments arguments) {
        this.limit = arguments.limit;
    }

    @Override
    boolean isCpxIntTrsApplicable(final CpxIntTrsProblem obl) {
        // All variables of the right-hand side and of the constraints
        // of a rule must also be present in its left-hand side.
        for (Map.Entry<CpxIntTupleRule, ComplexityValue> ruleToCpx : obl.getC()) {
            CpxIntTupleRule tupleRule = ruleToCpx.getKey();
            Set<TRSVariable> lhsVars = tupleRule.getLeft().getVariables();
            Set<TRSVariable> rhsVars = tupleRule.getRight().getVariables();
            rhsVars.removeAll(lhsVars);
            if (! rhsVars.isEmpty()) {
                return false;
            }
            @SuppressWarnings("unchecked")
            Set<TRSVariable> constraintVars =
                (Set<TRSVariable>)
                    aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(tupleRule.getConstraints());
            constraintVars.removeAll(lhsVars);
            if (! constraintVars.isEmpty()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public Result processCpxIntTrs(
        final CpxIntTrsProblem obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        try {
            // Thanks to isCpxIntTrsApplicable, we may conveniently
            // assume that the variable condition holds.
            RuntimeComplexityRelTrsProblem cpxRelTrs = this.convertCpxIntTrsToCpxRelTrs(obl, aborter);
            return ResultFactory.proved(cpxRelTrs, BothBounds.create(),
                    new CpxIntTrsToCpxRelTrsProof());
        } catch (IntOutOfRangeException e) {
            String message = "Transformation failed, because some integers"
                    + "were too big to be converted into pos/neg notation."
                    + "The offending value was " + e.getOffending()
                    + ", the limit was " + e.getLimit() + ".";
            CpxIntTrsToCpxRelTrsProcessor.log.info(message);
            return ResultFactory.unsuccessful(message);
        }
    }

    /**
     * @param obl - pass an obl on which isApplicable(obl) succeeds
     * @param aborter
     * @return a corresponding CpxRelTrsProblem with
     * @throws IntOutOfRangeException if the largest constant number exceeds our internal limit
     */
    private RuntimeComplexityRelTrsProblem convertCpxIntTrsToCpxRelTrs(final CpxIntTrsProblem obl, Abortion aborter)
                throws IntOutOfRangeException {

        // a small detour via IGeneralizedRules ...
        Set<IGeneralizedRule> iGenRules = CpxIntTupleRule.toIGeneralizedRules(obl.getK().keySet());
        aborter.checkAbortion();

        // - Now unravel.
        Set<GeneralizedRule> genRulesWithPredefinedSymbols = IGeneralizedRule.removeConditions(iGenRules, false);

        // - Find out which symbols we should not be introducing.
        Set<HasFunctionSymbols> forbiddenSymbolsHaver = new LinkedHashSet<HasFunctionSymbols>();
        forbiddenSymbolsHaver.addAll(genRulesWithPredefinedSymbols);
        aborter.checkAbortion();

        // - And then eliminate predefined stuff.
        PredefinedFunctionsManagerNegPos npMan =
                PredefinedFunctionsManagerNegPos.create(IDPPredefinedMap.DEFAULT_MAP,
                        forbiddenSymbolsHaver, this.limit);
        aborter.checkAbortion();

        // - Put the result into a CpxRelTrs.
        Set<Rule> convertedRules = new LinkedHashSet<>(); // primary result
        Set<Rule> auxiliaryRules = new LinkedHashSet<>(); // for predefined stuff

        for (GeneralizedRule r : genRulesWithPredefinedSymbols) {
            TRSFunctionApplication newL = npMan.extractTerm(r.getLeft());
            TRSTerm newR = npMan.extractTerm(r.getRight());

            Rule rule = Rule.create(newL, newR);
            convertedRules.add(rule);
        }
        aborter.checkAbortion();

        // add rules for predefined functions
        Set<Rule> rulesForPredefs = npMan.getGeneratedRules();
        auxiliaryRules.addAll(rulesForPredefs);

        ImmutableSet<Rule> R = ImmutableCreator.create(convertedRules);
        ImmutableSet<Rule> S = ImmutableCreator.create(auxiliaryRules);
        RuntimeComplexityRelTrsProblem resProblem =
                RuntimeComplexityRelTrsProblem.create(R, S, RewriteStrategy.INNERMOST, false);
        return resProblem;
    }

    public static class CpxIntTrsToCpxRelTrsProof extends Proof.DefaultProof {

        public CpxIntTrsToCpxRelTrsProof() {}

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Unraveled constraints and replaced predefined symbols by recursive rules.";
        }
    }

    public static class Arguments {
        /** max absolute value of integer literal accepted for conversion */
        public int limit = 1023;
    }
}
