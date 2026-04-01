package aprove.verification.oldframework.BasicStructures;

import java.util.*;

/**
 * Objects with FunctionSymbols can return the set of FunctionSymbols they are containing.
 * Created on 12.04.2005.
 * @author unknown, cryingshadow
 * @version $Id$
 */
public interface HasFunctionSymbols {

    /**
     * @return The set of FunctionSymbols of this. Must not be null.
     */
    public Set<FunctionSymbol> getFunctionSymbols();

}
