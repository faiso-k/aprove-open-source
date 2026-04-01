package aprove.verification.oldframework.SMT;

/**
 * Logics supported by SMT-LIB Version 2.
 * <p>
 * Descriptions shamelessly copied from <a
 * href="http://smtlib.cs.uiowa.edu/logics.shtml">SMT-LIB Homepage</a>.
 */
public enum SMTLIBLogic {
    /**
     * Closed formulas over the theory of linear integer arithmetic and arrays
     * extended with free sort and function symbols but restricted to arrays
     * with integer indices and values.
     */
    AUFLIA,
    /**
     * Closed linear formulas with free sort and function symbols over one- and
     * two-dimentional arrays of integer index and real value.
     */
    AUFLIRA,
    /**
     * Closed formulas with free function and predicate symbols over a theory of
     * arrays of arrays of integer index and real value.
     */
    AUFNIRA,
    /** Closed linear formulas in linear real arithmetic. */
    LRA,
    /**
     * Closed quantifier-free formulas over the theory of bitvectors and
     * bitvector arrays.
     */
    QF_ABV,
    /**
     * Closed quantifier-free formulas over the theory of bitvectors and
     * bitvector arrays extended with free sort and function symbols.
     */
    QF_AUFBV,
    /**
     * Closed quantifier-free linear formulas over the theory of integer arrays
     * extended with free sort and function symbols.
     */
    QF_AUFLIA,
    /**
     * Closed quantifier-free formulas over the theory of arrays with
     * extensionality.
     */
    QF_AX,
    /**
     * Closed quantifier-free formulas over the theory of fixed-size bitvectors.
     */
    QF_BV,
    /**
     * Difference Logic over the integers. In essence, Boolean combinations of
     * inequations of the form x - y < b where x and y are integer variables and
     * b is an integer constant.
     */
    QF_IDL,
    /**
     * Unquantified linear integer arithmetic. In essence, Boolean combinations
     * of inequations between linear polynomials over integer variables.
     */
    QF_LIA,
    /**
     * Unquantified linear real arithmetic. In essence, Boolean combinations of
     * inequations between linear polynomials over real variables.
     */
    QF_LRA,
    /** Quantifier-free integer arithmetic. */
    QF_NIA,
    /** Quantifier-free real arithmetic. */
    QF_NRA,
    /**
     * Difference Logic over the reals. In essence, Boolean combinations of
     * inequations of the form x - y < b where x and y are real variables and b
     * is a rational constant.
     */
    QF_RDL,
    /**
     * Unquantified formulas built over a signature of uninterpreted (i.e.,
     * free) sort and function symbols.
     */
    QF_UF,
    /**
     * Unquantified formulas over bitvectors with uninterpreted sort function
     * and symbols.
     */
    QF_UFBV,
    /**
     * Difference Logic over the integers (in essence) but with uninterpreted
     * sort and function symbols.
     */
    QF_UFIDL,
    /**
     * Unquantified linear integer arithmetic with uninterpreted sort and
     * function symbols.
     */
    QF_UFLIA,
    /**
     * Unquantified linear real arithmetic with uninterpreted sort and function
     * symbols.
     */
    QF_UFLRA,
    /**
     * Unquantified non-linear real arithmetic with uninterpreted sort and
     * function symbols.
     */
    QF_UFNRA,
    /** Linear real arithmetic with uninterpreted sort and function symbols. */
    UFLRA,
    /**
     * Non-linear integer arithmetic with uninterpreted sort and function
     * symbols.
     */
    UFNIA;
}
