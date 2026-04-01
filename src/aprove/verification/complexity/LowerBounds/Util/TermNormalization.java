package aprove.verification.complexity.LowerBounds.Util;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public class TermNormalization {

    public static BidirectionalMap<TRSVariable, TRSVariable> getRenamingMapForVariables(TRSTerm... terms) {
        int next = 0;
        BidirectionalMap<TRSVariable, TRSVariable> renaming = new BidirectionalMap<>();
        for (TRSTerm t : terms) {
            for (TRSVariable x : t.getVariables()) {
                if (!renaming.containsKeyLR(x)) {
                    renaming.putLR(x, TRSTerm.createVariable("x" + next));
                    next++;
                }
            }
        }
        return renaming;
    }

    public static BidirectionalMap<TRSTerm, TRSTerm> getRenamingMapForConstants(TRSTerm... terms) {
        int next = 0;
        BidirectionalMap<TRSTerm, TRSTerm> renaming = new BidirectionalMap<>();
        for (TRSTerm t : terms) {
            for (FunctionSymbol x : t.getFunctionSymbols()) {
                if (x.getArity() == 0) {
                    TRSFunctionApplication funApp = TRSTerm.createFunctionApplication(x);
                    if (!PFHelper.isInt(funApp)) {
                        if (!renaming.containsKeyLR(funApp)) {
                            renaming.putLR(funApp, TRSTerm.createFunctionApplication(FunctionSymbol.create("c" + next, 0)));
                            next++;
                        }
                    }
                }
            }
        }
        return renaming;
    }

}
