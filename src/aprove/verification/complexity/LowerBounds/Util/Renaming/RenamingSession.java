package aprove.verification.complexity.LowerBounds.Util.Renaming;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;


public class RenamingSession {

    private RenamingCentral renamingCentral;
    private Map<String, TRSVariable> varCache = new LinkedHashMap<>();
    private Map<String, FunctionSymbol> symbolCache = new LinkedHashMap<>();

    public RenamingSession(RenamingCentral renamingCentral) {
        this.renamingCentral = renamingCentral;
    }

    public TRSVariable renameVariable(TRSVariable x) {
        return this.freshVariable(x.getName());
    }

    public TRSVariable freshVariable(String oldName) {
        if (this.varCache.containsKey(oldName)) {
            return this.varCache.get(oldName);
        } else {
            TRSVariable res = TRSTerm.createVariable(this.renamingCentral.getFreshName(oldName));
            this.varCache.put(oldName, res);
            return res;
        }
    }

    public FunctionSymbol renameSymbol(FunctionSymbol f) {
        return this.freshSymbol(f.getName(), f.getArity());
    }

    public FunctionSymbol freshConstant(String oldName) {
        return this.freshSymbol(oldName, 0);
    }

    public FunctionSymbol freshSymbol(String oldName, int arity) {
        FunctionSymbol res;
        if (this.symbolCache.containsKey(oldName)) {
            res =this.symbolCache.get(oldName);
            assert res.getArity() == arity;
        } else {
            res = FunctionSymbol.create(this.renamingCentral.getFreshName(oldName), arity);
            this.symbolCache.put(oldName, res);
        }
        return res;
    }

    public Map<TRSTerm, TRSTerm> rename(Set<TRSVariable> toRename) {
        Map<TRSTerm, TRSTerm> res = new LinkedHashMap<>();
        for (TRSVariable var: toRename) {
            res.put(var, this.renameVariable(var));
        }
        return res;
    }

}
