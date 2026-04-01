package aprove.verification.dpframework.CLSProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

public class CLSPredefinedNameProvider implements NameProvider {

    private static final Set<String> PREDEFINED;

    static {
        PREDEFINED = new HashSet<String>();
        for(FunctionSymbol sym : PredefinedHelper.PREDEF_SYMS) {
            CLSPredefinedNameProvider.PREDEFINED.add(sym.getName());
        }
    }

    @Override
    public boolean contains(String name) {
        return CLSPredefinedNameProvider.PREDEFINED.contains(name) || PredefinedHelper.isInt(name);
    }

}
