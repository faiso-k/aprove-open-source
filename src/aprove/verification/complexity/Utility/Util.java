package aprove.verification.complexity.Utility;

import java.util.*;

import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class Util {

    public static TRSTerm linearizeAndAbstractInnerOccurrencesOf(TRSFunctionApplication t, Set<FunctionSymbol> toAbstract, RenamingCentral renamingCentral) {
        TRSTerm res = normalize(linearize(t, t.getVariables(), renamingCentral));
        boolean changed;
        do {
            changed = false;
            for (Pair<Position, TRSFunctionApplication> p: res.getNonRootNonVariablePositionsWithSubTerms()) {
                Position pi = p.x;
                TRSFunctionApplication s = p.y;
                FunctionSymbol f = s.getRootSymbol();
                if (toAbstract.contains(f)) {
                    res = normalize(res.replaceAt(pi, renamingCentral.freshVariable("x")));
                    changed = true;
                    break;
                }
            }
        } while (changed);
        return res;
    }

    public static TRSTerm normalize(TRSTerm t) {
        return t.renameVariables(TermNormalization.getRenamingMapForVariables(t).getLRMap());
    }

    public static TRSTerm linearize(TRSTerm tArg, Collection<TRSVariable> vars, RenamingCentral renamingCentral) {
        TRSTerm t = tArg;
        Map<TRSVariable, List<Position>> varPositions = t.getVariablePositions();
        for (TRSVariable x: vars) {
            List<Position> positions = varPositions.get(x);
            if (positions.size() > 1) {
                boolean first = true;
                for (Position pi: positions) {
                    if (first) {
                        first = false;
                        continue;
                    }
                    t = t.replaceAt(pi, renamingCentral.freshVariable(x.getName()));
                }
            }
        }
        return t;
    }

}
