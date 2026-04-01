package aprove.verification.oldframework.Rewriting;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;

/** Interface for evaluators.
 * @author Eugen Yu
 * @version $Id$
 */

public interface Evaluator {

    public static int NO_RULES_FOR_CONSTRUCTOR = 0; //this is the default value
    public static int THERE_ARE_RULES_FOR_CONSTRUCTOR = 1;

    /** Evaluate a term to its p-normal form.
     * @param t is the term to be evaluated.
     * @return A Term evaluated as far as possible.
     */
    public AlgebraTerm eval(AlgebraTerm t);

    /**
     * Check whether a term can be evaluated.
     * Right now not optimized because this check do parts of things that eval function also does
     *
     */
    public boolean evaluable(AlgebraTerm t);


    /**
     * Check whether a formula can be evaluated.
     */
    public boolean evaluable(Formula f);


}
