package aprove.verification.oldframework.IntegerReasoning;

import java.math.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A triple (x,y,z) with the meaning x <= y <= z for two constants x and z and a variable y. One of the constants may
 * be null - then the corresponding constant is replaced by (-)infinity.
 * @author cryingshadow
 * @version $Id$
 */
public class BoundInfo extends Triple<BigInteger, IntegerVariable, BigInteger> {

    /**
     * @param lower The lower bound.
     * @param var The variable.
     * @param upper The upper bound.
     */
    public BoundInfo(BigInteger lower, IntegerVariable var, BigInteger upper) {
        super(lower, var, upper);
    }

}
