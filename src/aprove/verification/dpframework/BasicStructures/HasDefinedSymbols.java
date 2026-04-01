package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;

/**
 * Objects with defined symbols can return the set of all its defined symbols.
 */
public interface HasDefinedSymbols {

    Set<FunctionSymbol> getDefinedSymbols();

}
