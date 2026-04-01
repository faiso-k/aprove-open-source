/*
 * Created on 12.04.2005
 */
package aprove.verification.oldframework.BasicStructures;

import java.util.*;

/**
 * Objects containing Variables can offer them as a set.
 * @author unknown, cryingshadow
 * @version $Id$
 */
public interface HasVariables {

    /**
     * @return The set of variables occurring in this object. Must return non-null value.
     */
    Set<? extends Variable> getVariables();

}
