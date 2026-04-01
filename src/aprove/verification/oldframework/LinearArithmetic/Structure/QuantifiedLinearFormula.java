package aprove.verification.oldframework.LinearArithmetic.Structure;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public abstract class QuantifiedLinearFormula extends LinearFormula{

    protected AlgebraVariable variable;

    protected LinearFormula subFormula;

    /**
     * @return the subForumla
     */
    public LinearFormula getSubFormula() {
        return this.subFormula;
    }

    /**
     * @return the variable
     */
    public AlgebraVariable getVariable() {
        return this.variable;
    }

}
