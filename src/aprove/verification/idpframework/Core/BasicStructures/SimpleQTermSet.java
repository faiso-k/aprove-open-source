/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.BasicStructures;

import java.util.*;

public interface SimpleQTermSet {

    /**
     * checks whether all lhs of the rules in the collection can be rewritten
     * @param lhsR
     * @return
     */
    public boolean canAllLhsBeRewritten(Set<? extends IRule> R);

    /**
     * checks whether all terms in the collection can be rewritten
     * @param lhsR
     * @return
     */
    public boolean canAllBeRewritten(Collection<? extends ITerm<?>> terms);

    /**
     * checks whether t can be rewritten
     * @param t
     */
    public boolean canBeRewritten(ITerm<?> t);

    public boolean canBeRewrittenAtRoot(IFunctionApplication<?> t);

    /**
     * checks whether some term of terms can be rewritten
     * @param terms
     */
    public boolean someTermCanBeRewritten(Iterable<? extends ITerm<?>> terms);

    /**
     * Checks whether some proper subterm of <code>t</code> can be rewritten
     */
    public boolean canBeRewrittenBelowRoot(ITerm<?> t);

}