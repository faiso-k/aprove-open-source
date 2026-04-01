package aprove.verification.complexity.CpxITrsProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxITrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfManager.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Converts an ITRSProblem to an QTRSProblem.
 *
 * This is done by converting integers (and the predefined functions) to a
 * pos-neg representation.
 */
public class CpxITrsToCdtProcessor extends CpxITrsProcessor {

    private static Logger log = Logger.getLogger(CpxITrsProcessor.class
            .getCanonicalName());

    /**
     * On which ITRSs do we want to be applicable?
     */
    private final ToTermApplicability apply;

    /**
     * What is the highest absolute value of an integer literal allowed for
     * explicit conversion?
     */
    private final int limit;

    @ParamsViaArgumentObject
    public CpxITrsToCdtProcessor(final Arguments arguments) {
        this.apply = arguments.apply;
        this.limit = arguments.limit;
    }

    /**
     * Checks if this processor is applicable to the ITRS.
     *
     * The result depends on the parameter "apply" of the processor.
     */
    @Override
    protected boolean isCpxITrsApplicable(final CpxITrsProblem cpxitrs) {
        final RuleAnalysis<GeneralizedRule> ruleA = cpxitrs.getRuleAnalysis();
        switch (this.apply) {
        case NOPREDEFS: {
            if (!ruleA.getPredefinedFunctions().isEmpty()) {
                return false;
            }
            break;
        }
        case CONSTONLY: {
            if (ruleA.hasPredefinedDefSymbols()) {
                return false;
            }
            break;
        }
        case ALWAYS: {
            break;
        }
        default:
            throw new aprove.verification.oldframework.Exceptions.NotYetHandledException(
                    "Check for " + this.apply + " not handled yet!");
        }
        return !ruleA.hasRestrictedInt() && !ruleA.hasBitwiseOps()
                && ruleA.satVarCondition();
    }

    @Override
    protected Result processCpxITrs(final CpxITrsProblem itrs, final Abortion aborter)
            throws AbortionException {
        try {
            final CdtProblem cdt = this.convertCpxITrsToCDT(itrs);
            return ResultFactory.proved(cdt, BothBounds.create(),
                    new CpxITrsToCdtProof());
        } catch (final IntOutOfRangeException e) {
            final String message = "Transformation failed, because some integers"
                    + "were too big to be converted into pos/neg notation."
                    + "The offending value was " + e.getOffending()
                    + ", the limit was " + e.getLimit() + ".";
            CpxITrsToCdtProcessor.log.warning(message);
            return ResultFactory.error(message);
        }
    }

    public CdtProblem convertCpxITrsToCDT(final CpxITrsProblem cpxitrs)
            throws IntOutOfRangeException {

        final ImmutableSet<TRSFunctionApplication> explicitOrigQTerms = cpxitrs.getQ()
                .getExplicitTerms();

        // beware of name clashes
        final Set<HasFunctionSymbols> forbiddenSymbols = new LinkedHashSet<HasFunctionSymbols>();
        forbiddenSymbols.addAll(explicitOrigQTerms);
        forbiddenSymbols.addAll(cpxitrs.getR());

        final PredefinedFunctionsManagerNegPos npMan = PredefinedFunctionsManagerNegPos
                .create(cpxitrs.getRuleAnalysis().getPreDefinedMap(),
                        forbiddenSymbols, this.limit);

        // Use linked sets here just for user-friendliness. We want the
        // transformed "real" rules first and the generated rules last.
        final Set<Rule> rules = new LinkedHashSet<Rule>();

        for (final GeneralizedRule r : cpxitrs.getR()) {
            final TRSFunctionApplication newL = npMan.extractTerm(r.getLeft());
            final TRSTerm newR = npMan.extractTerm(r.getRight());

            final Rule rule = Rule.create(newL, newR);

            rules.add(rule);
        }

        // build Q
        final Set<TRSFunctionApplication> qTerms = new LinkedHashSet<TRSFunctionApplication>(
                explicitOrigQTerms.size());

        // postprocess those qTerms by npMan, too
        for (final TRSFunctionApplication origQTerm : explicitOrigQTerms) {
            final TRSFunctionApplication newQTerm = npMan.extractTerm(origQTerm);
            qTerms.add(newQTerm);
        }

        // add rules for predefined functions
        final Set<Rule> rulesForPredefs = npMan.getGeneratedRules();
        rules.addAll(rulesForPredefs);
        qTerms.addAll(aprove.verification.dpframework.BasicStructures.CollectionUtils
                .getLeftHandSides(rulesForPredefs));

        final Set<FunctionSymbol> defSyms = CollectionUtils
                .getRootSymbols(cpxitrs.getR());

        return CdtProblem.create(rules, defSyms).y;
    }

    public class CpxITrsToCdtProof extends DefaultProof {
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            // FIXME: Make a real proof?
            return "Represented integers and predefined function symbols by Terms";
        }
    }

    public static class Arguments {
        // when do we want to be applicable?
        public ToTermApplicability apply = ToTermApplicability.ALWAYS;

        // max absolute value of integer literal accepted for conversion
        public int limit = 1023;
    }
}
