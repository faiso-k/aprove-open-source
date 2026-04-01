package aprove.verification.dpframework.DPProblem.Processors;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPProblem.*;

/**
 * Rule Removal processor. Using a POLO, tries to orient all rules of P
 * and R non-strictly and at least one rule of P or R strictly, then
 * deletes the strictly oriented rules. (See Theorem 30 of LPAR04.)
 *
 * Legacy processor to maintain compatibility with old strategies. Now
 * superseded by MRRProcessor, to which calls to this processor are
 * delegated.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class RuleRemovalProcessor extends QDPProblemProcessor {

    /** Does the actual work for this legacy processor. */
    private final MRRProcessor genericMRRProc;

    @ParamsViaArgumentObject
    public RuleRemovalProcessor(final AbstractStrictPoloQDPProblemProcessor.Arguments arguments) {
        final boolean allstrict = arguments.mode == PoloStrictMode.ALLSTRICT;
        final POLOFactory.Arguments facArgs = new POLOFactory.Arguments();
        facArgs.autostrict = arguments.mode == PoloStrictMode.AUTOSTRICT;
        facArgs.autostrictJar = true; // be legacy compliant
        facArgs.degree = arguments.degree;
        facArgs.engine = arguments.engine;
        facArgs.linearMonotone = false;
        facArgs.maxSimpleDegree = arguments.maxSimpleDegree;
        facArgs.range = arguments.range;
        facArgs.satConverter = arguments.satConverter;
        facArgs.simplification = arguments.simplification;
        facArgs.simplifyAll = arguments.simplifyAll;
        facArgs.stripExponents = arguments.stripExponents;
        final POLOFactory factory = new POLOFactory(facArgs);
        this.genericMRRProc = new MRRProcessor(factory, allstrict);
    }

    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter)
            throws AbortionException {
        return this.genericMRRProc.processQDPProblem(qdp, aborter);
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return this.genericMRRProc.isQDPApplicable(qdp);
    }
}
