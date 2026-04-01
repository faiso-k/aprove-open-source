package aprove.verification.dpframework.TRSProblem.Processors;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;

/**
 * Remove Redundant Rules Polo Processor. Given a QTRS, tries to
 * orient all rules non-strictly and at least one of them strictly,
 * then removes the strictly oriented rules.
 *
 * Legacy processor to maintain compatibility with old strategies. Now
 * superseded by QTRSRRRProcessor, to which calls to this processor are
 * delegated.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class RRRPoloProcessor extends QTRSProcessor {

    /** Does the actual work for this legacy processor. */
    private final QTRSRRRProcessor genericRRRProc;

    @ParamsViaArgumentObject
    public RRRPoloProcessor (final Arguments arguments) {
        final POLOFactory.Arguments facArgs = new POLOFactory.Arguments();
        facArgs.autostrict = arguments.autostrict;
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
        this.genericRRRProc = new QTRSRRRProcessor(factory);
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.TRSProblem.Processors.QTRSProcessor#processQTRS(aprove.verification.dpframework.TRSProblem.QTRSProblem, aprove.strategies.Abortions.Abortion)
     */
    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti)
            throws AbortionException {
        return this.genericRRRProc.processQTRS(qtrs, aborter, rti);
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.TRSProblem.Processors.QTRSProcessor#isQTRSApplicable(aprove.verification.dpframework.TRSProblem.QTRSProblem)
     */
    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return this.genericRRRProc.isQTRSApplicable(qtrs);
    }


    public static class Arguments {
        public boolean autostrict = false;
        public int degree;
        public Engine engine;
        public int maxSimpleDegree;
        public int range;
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean simplifyAll;
        public boolean stripExponents;
    }
}
