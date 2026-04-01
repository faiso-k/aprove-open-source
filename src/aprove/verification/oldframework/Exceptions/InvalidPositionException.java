package aprove.verification.oldframework.Exceptions;
import aprove.verification.oldframework.Algebra.Terms.*;

/** Exception thrown by methods which use position of a term or formula, eventually term as well
 * @author Eugen Yu
 */

public class InvalidPositionException extends Exception {
    protected Position p;

    public InvalidPositionException(Position pos, String s) {
        super(s);
    this.p=pos;
    }

    public Position getPosition(){
    return this.p;
    }

}
