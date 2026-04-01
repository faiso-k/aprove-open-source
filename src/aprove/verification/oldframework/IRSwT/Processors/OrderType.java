package aprove.verification.oldframework.IRSwT.Processors;

/**
 * Enumeration of currently supported orders.
 * @author Matthias Hoelzel
 */
public enum OrderType {
    /** Find a suitable interpretation. */
    INTERPRETATION,
    /** Embedding order. Just for fun! */
    EMB_SOLVER,
    /** LPO with status via depth search. */
    LPOS_DEPTH_SOLVER,
    /** LPO without status via depth search. */
    LPO_DEPTH_SOLVER,
    /** LPO with status via breadth search. */
    LPOS_BREADTH_SOLVER,
    /** LPO without status via breadth search. */
    LPO_BREADTH_SOLVER,
    /** Knuth-Bendix order. */
    KBO_SOLVER,
    /** Knuth-Bendix with some polynomials (?) */
    KBO_POLO_SOLVER,
    /** Knuth-Bendix with some polynomials and more funny things (?) */
    KBO_POLO_SMT_SOLVER,
    /** Polynomial interpretation over strange arctic numbers */
    ARCTIC_POLO,
    /** QLPO with status via depth search. */
    QLPOS_DEPTH_SOLVER,
    /** QLPO with status via breadth search. */
    QLPOS_BREADTH_SOLVER,
    /** QLPO without status via depth search. */
    QLPO_DEPTH_SOLVER,
    /** QLPO without status via breadth search. */
    QLPO_BREADTH_SOLVER,
    /** RPO with status via depth search. */
    RPOS_DEPTH_SOLVER,
    /** RPO with status via breadth search. */
    RPOS_BREADTH_SOLVER,
    /** RPO without status via depth search. */
    RPO_DEPTH_SOLVER,
    /** RPO without status via breadth search. */
    RPO_BREADTH_SOLVER,
    /** QRPO with status via depth search. */
    QRPOS_DEPTH_SOLVER,
    /** QRPO with status via breadth search. */
    QRPOS_BREADTH_SOLVER,
    /** QRPO without status via depth search. */
    QRPO_DEPTH_SOLVER,
    /** QRPO without status via breadth search. */
    QRPO_BREADTH_SOLVER;

}
