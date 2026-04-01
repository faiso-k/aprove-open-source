package aprove.verification.dpframework;

/**
 * Different types of AFS' used by DP problem solvers
 * @author Andreas Kelle-Emden
 */
public enum AFSType {
    NOAFS,       // Do not use any AFS (i.e. force strong monotonicity)
    MONOTONEAFS, // Only funtionsymbols with arity 1 may be collapsed, no arguments are filtered
    FULLAFS      // Any argument filtering may be used
}
