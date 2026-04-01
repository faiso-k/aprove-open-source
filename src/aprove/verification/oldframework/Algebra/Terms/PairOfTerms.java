package aprove.verification.oldframework.Algebra.Terms;



/** Interface and abstract class for a pair of terms.
 *  Skeleton provides a default implementation of some methods.
 *  See Terms.Rewriting.Rule, Logic.Formulas.Equation for other implementations.
 * @author Eugen yu, Burak Emir, Peter Schneider-Kamp
 * @version $Id$
 */

public interface PairOfTerms {

    /** Returns the left component of a pair of terms.
     */
    public AlgebraTerm getLeft();

    /** Returns the right component of a pair of terms.
     */
    public AlgebraTerm getRight();

    /** Check whether this pair of terms equals another pair of terms.
     */
    @Override
    public boolean equals( Object o );

}
