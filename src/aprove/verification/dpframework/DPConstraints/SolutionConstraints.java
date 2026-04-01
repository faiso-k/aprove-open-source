package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public class SolutionConstraints {

    public final boolean multiSet;

    public final Set<FunctionSymbol> symbolsAllowed;

    public boolean checkReplacement(TRSTerm t) {
        return this.symbolsAllowed.containsAll(t.getFunctionSymbols());
    }

    public SolutionConstraints(Set<FunctionSymbol> symbolsAllowed, boolean multiSet) {
        super();
        this.symbolsAllowed = symbolsAllowed;
        this.multiSet = multiSet;
    }

}
