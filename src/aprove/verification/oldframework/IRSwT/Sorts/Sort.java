package aprove.verification.oldframework.IRSwT.Sorts;

/**
 * Represents what we can deduce about the sort/type of some term.
 * @author Matthias Hoelzel
 *
 */
public enum Sort {
    /**
     * sort describing only variables
     */
    VARIABLE,

    /**
     * sort describing only function applications and variables
     */
    FUNAPP,

    /**
     * sort describing only integers and variables
     */
    INTEGER,

    /**
     * sort describing function application, integers, variables, everything
     */
    EVERYTHING;
}
