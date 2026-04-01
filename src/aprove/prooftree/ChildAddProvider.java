package aprove.prooftree;

import java.util.*;

import aprove.prooftree.Obligations.*;

/**
 * Created on Jun 1, 2005 by marmer
 *
 * @author marmer
 * @version $Id$
 */

public interface ChildAddProvider {

    /**
     * Registers a listener that will be called each time we get a child.
     * @return our current children. Atomic guarantee is that you will not
     * get called on any of those, and will get called on any further children.
     */
    public Collection<ObligationNodeChild> addChildAddListener(
            ChildAddListener listener);
    public void removeChildAddListener(ChildAddListener listener);

}
