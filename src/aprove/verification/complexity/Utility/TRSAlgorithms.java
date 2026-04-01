package aprove.verification.complexity.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public class TRSAlgorithms {
    /**
     * Checks if R is an constructor system, i.e. all function symbols on
     * the lhs below the root symbols are constructor symbols.
     */
    public static boolean isConstructorSystem(Set<Rule> rules,
            Set<FunctionSymbol> definedSymbols) {
        for (Rule r : rules) {
            for (TRSTerm t : r.getLeft().getArguments()) {
                Set<FunctionSymbol> termSyms = t.getFunctionSymbols();
                for (FunctionSymbol fs : termSyms) {
                    if (definedSymbols.contains(fs)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

}
