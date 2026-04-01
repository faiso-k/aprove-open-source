package aprove.verification.oldframework.LinearArithmetic.Structure;

/**
 * Enum for the type of a constraint.
 *
 * @author dickmeis
 * @version $Id$
 */

public enum ConstraintType {
    EQUALITY, INEQUALITY, LESS, LESSEQ, GREATER, GREATEREQ;

    @Override
    public String toString(){
        switch (this) {
            case EQUALITY:
                return "=";
            case INEQUALITY:
                return "!=";
            case LESS:
                return "<";
            case LESSEQ:
                return "<=";
            case GREATER:
                return ">";
            case GREATEREQ:
                return ">=";

            default:
                return this.name();
            }

    }
}
