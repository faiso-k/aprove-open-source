package aprove.verification.dpframework.BasicStructures;

import java.util.*;

/**
 * Objects with TRSTerms can return the set of TRSTerms they are containing.
 * Created on 12.04.2005.
 * @author unknown, cryingshadow
 * @version $Id$
 */
public interface HasTRSTerms {

    /**
     * @return The set of terms of this. Must not be null.
     */
    public Set<? extends TRSTerm> getTerms();

}
