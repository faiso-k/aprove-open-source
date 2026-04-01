/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfManager.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/** Converts an ITRSProblem to an QTRSProblem.
 *
 * This is done by converting integers (and the predefined functions)
 * to a pos-neg representation.
 */
public class ITRStoQTRSProcessor extends ITRSProcessor {

    private static Logger log = Logger.getLogger("aprove.verification.dpframework.IDPProblem.Processors.ITRStoQTRSProcessor");

    /**
     * On which ITRSs do we want to be applicable?
     */
    private final ToTermApplicability apply;

    /**
     * true: generate a QTRS with Q = LHS(R)
     * false: generate a QTRS with Q = \emptyset
     */
    private final boolean innermost;

    /**
     * What is the highest absolute value of an integer literal allowed for
     * explicit conversion?
     */
    private final int limit;

    @ParamsViaArgumentObject
    public ITRStoQTRSProcessor(Arguments arguments) {
        this.apply = arguments.apply;
        this.limit = arguments.limit;
        this.innermost = arguments.innermost;
    }

    /** Checks if this processor is applicable to the ITRS.
     *
     * The result depends on the parameter "apply" of the processor.
     */
    @Override
    public boolean isITRSApplicable(ITRSProblem itrs) {
        RuleAnalysis<GeneralizedRule> ruleA = itrs.getRuleAnalysis();
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
            throw new aprove.verification.oldframework.Exceptions.NotYetHandledException("Check for "
                    + this.apply + " not handled yet!");
        }
        return !ruleA.hasRestrictedInt()
            && !ruleA.hasBitwiseOps()
            && ruleA.satVarCondition();

    }

    @Override
    protected Result processITRSProblem(ITRSProblem itrs, Abortion aborter)
            throws AbortionException {
        try {
            QTRSProblem qtrs = this.ITRStoQTRS(itrs);
            if (this.innermost) {
                return ResultFactory.proved(qtrs, YNMImplication.EQUIVALENT,
                        new ITRStoQTRSProof());
            }
            else {
                qtrs = qtrs.createTermination();
                return ResultFactory.proved(qtrs, YNMImplication.SOUND,
                        new ITRStoQTRSProof());
            }
        } catch (IntOutOfRangeException e) {
            String message = "Transformation failed, because some integers" +
                    "were too big to be converted into pos/neg notation." +
                    "The offending value was " + e.getOffending() +
                    ", the limit was " + e.getLimit() + ".";
            ITRStoQTRSProcessor.log.warning(message);
            return ResultFactory.error(message);
        }
    }

    public QTRSProblem ITRStoQTRS(final ITRSProblem itrs)
            throws IntOutOfRangeException {

        ImmutableSet<TRSFunctionApplication> explicitOrigQTerms =
            itrs.getQ().getExplicitTerms();

        // beware of name clashes
        Set<HasFunctionSymbols> forbiddenSymbols = new LinkedHashSet<HasFunctionSymbols>();
        forbiddenSymbols.addAll(explicitOrigQTerms);
        forbiddenSymbols.addAll(itrs.getR());

        PredefinedFunctionsManagerNegPos npMan =
            PredefinedFunctionsManagerNegPos.create(itrs.getRuleAnalysis().getPreDefinedMap(), forbiddenSymbols, this.limit);

        // Use linked sets here just for user-friendliness. We want the
        // transformed "real" rules first and the generated rules last.
        Set<Rule> rules = new LinkedHashSet<Rule>();

        for (GeneralizedRule r : itrs.getR()) {
            TRSFunctionApplication newL = npMan.extractTerm(r.getLeft());
            TRSTerm newR = npMan.extractTerm(r.getRight());

            Rule rule =
                Rule.create(newL, newR);

            rules.add(rule);
        }

        // build Q
        Set<TRSFunctionApplication> qTerms =
            new LinkedHashSet<TRSFunctionApplication>(explicitOrigQTerms.size());

        // postprocess those qTerms by npMan, too
        for (TRSFunctionApplication origQTerm : explicitOrigQTerms) {
            TRSFunctionApplication newQTerm = npMan.extractTerm(origQTerm);
            qTerms.add(newQTerm);
        }

        // add rules for predefined functions
        Set<Rule> rulesForPredefs = npMan.getGeneratedRules();
        rules.addAll(rulesForPredefs);
        qTerms.addAll(aprove.verification.dpframework.BasicStructures.CollectionUtils.getLeftHandSides(rulesForPredefs));

        return QTRSProblem.create(ImmutableCreator.create(rules), qTerms);
    }



    public class ITRStoQTRSProof extends DefaultProof {
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME: Make a real proof?
            return "Represented integers and predefined function symbols by Terms";
        }
    }

    public static class Arguments {
        // when do we want to be applicable?
        public ToTermApplicability apply = ToTermApplicability.ALWAYS;

        // max absolute value of integer literal accepted for conversion
        public int limit = 1023;

        // true: generate a QTRS with Q = LHS(R)
        // false: generate a QTRS with Q = \emptyset
        public boolean innermost = true;
    }
}
