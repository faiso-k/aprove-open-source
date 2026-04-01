/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.BasicStructures;

import java.util.*;

public interface SimpleQTermSet {

    /**
     * checks whether all lhs of the rules in the collection can be rewritten
     * @param R is a rule like object with a lhs
     * @return
     */
    public boolean canAllLhsBeRewritten(Set<? extends HasLHS> R);

    /**
     * checks whether all terms in the collection can be rewritten
     * @param lhsR
     * @return
     */
    public boolean canAllBeRewritten(Collection<TRSFunctionApplication> terms);

    /**
     * checks whether t can be rewritten
     * @param t
     */
    public boolean canBeRewritten(TRSTerm t);

    public boolean canBeRewrittenAtRoot(TRSFunctionApplication t);

    /**
     * checks whether some term of terms can be rewritten
     * @param terms
     */
    public boolean someTermCanBeRewritten(Iterable<? extends TRSTerm> terms);

    /**
     * Checks whether some proper subterm of <code>t</code> can be rewritten
     */
    public boolean canBeRewrittenBelowRoot(TRSTerm t);

}