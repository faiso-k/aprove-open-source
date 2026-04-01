package aprove.verification.dpframework.Orders ;

import aprove.verification.dpframework.Orders.Utility.*;

/** Abstract class for an StrictOrderOnTerms that can be used by MultisetExtension.
 *
 * @author Stephan Falke
 * @version $Id$
 */

public interface MultisetExtensibleOrder<T> extends Order<T> {

    /** Returns on of the constants defined in Relation.
     */
    public abstract OrderRelation compare(T s, T t);

}
