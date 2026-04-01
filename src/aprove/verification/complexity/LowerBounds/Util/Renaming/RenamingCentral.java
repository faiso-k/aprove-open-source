package aprove.verification.complexity.LowerBounds.Util.Renaming;

import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public class RenamingCentral {

    private long suffix = 0;
    private long next = 0;

    public static RenamingCentral create(Set<? extends HasName> lockedNames) {
        return new RenamingCentral(lockedNames.stream().map(x -> x.getName()).collect(toSet()));
    }

    public RenamingCentral(Set<String> lockedNames) {
        boolean found;
        do {
            found = false;
            for (String locked: lockedNames) {
                if (locked.endsWith(Long.toString(this.suffix))) {
                    this.suffix++;
                    found = true;
                    break;
                }
            }
        } while (found);
    }

    String getFreshName(String old) {
        this.next++;
        return old + this.next + "_" + this.suffix;
    }

    public TRSVariable renameVariable(TRSVariable x) {
        return this.freshVariable(x.getName());
    }

    public TRSVariable freshVariable(String oldName) {
        return TRSTerm.createVariable(this.getFreshName(oldName));
    }

    public FunctionSymbol renameSymbol(FunctionSymbol f) {
        return this.freshSymbol(f.getName(), f.getArity());
    }

    public FunctionSymbol freshConstant(String oldName) {
        return this.freshSymbol(oldName, 0);
    }

    public FunctionSymbol freshSymbol(String oldName, int arity) {
        return FunctionSymbol.create(this.getFreshName(oldName), arity);
    }

    public RenamingSession getSession() {
        return new RenamingSession(this);
    }

    public BidirectionalMap<TRSTerm, TRSTerm> mapVariablesToFreshConstants(Set<TRSVariable> variables) {
        BidirectionalMap<TRSTerm, TRSTerm> replacementMap = new BidirectionalMap<>();
        for (TRSVariable other : variables) {
            TRSTerm replacement = TRSTerm.createFunctionApplication(this.freshConstant(other.getName()));
            replacementMap.putLR(other, replacement);
        }
        return replacementMap;
    }

}
