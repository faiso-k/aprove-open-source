package aprove.verification.dpframework.IDPProblem.utility;

/**
 * Parameter for processors that convert from integer TRSs/DP problems
 * to "conventional" TRSs/DP problems.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public enum ToTermApplicability {
    // apply as often as possible
    ALWAYS,

    // applicable iff there are no predefined defined symbols present
    CONSTONLY,

    // applicable iff there are no predefined symbols present
    // (neither defined symbols nor constructors)
    NOPREDEFS,

    // apply always, if needed, filter away free variables
    ALWAYSFILTER,
}
