package aprove.verification.idpframework.Core.Utility;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;

/**
 *
 * @author MP
 */
public interface HasVariables<V extends IVariable<?>> {

    public Collection<V> getVariables();

}
