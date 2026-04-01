package aprove.verification.oldframework.IntTRS.CaseAnalysis;

/**
 * Modes for the case analysis processor.
 * @author matthias
 *
 */
public enum CaseAnalysisMode {
    /**
     * First runs the heuristic and then it tries the SMT-based approach.
     */
    DEFAULT,
    /**
     * Only applies the change term heuristic.
     */
    ONLY_HEURISTIC,
    /**
     * Disables the heuristic.
     */
    ONLY_SMT;
}
