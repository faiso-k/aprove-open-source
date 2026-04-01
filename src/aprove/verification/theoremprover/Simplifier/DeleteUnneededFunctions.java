package aprove.verification.theoremprover.Simplifier;

import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Syntax.*;

@NoParams
public class DeleteUnneededFunctions extends SimplifierProcessor {

    public DeleteUnneededFunctions(){
        super("Delete Unneeded Functions","DUF","Delete Unneeded Functions");
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation oobl) {
        Set delFuncs = new HashSet();
        SimplifierObligation obl = oobl.shallowcopy();
    Set<DefFunctionSymbol> needed = new HashSet<DefFunctionSymbol>();
    Iterator it = obl.defs.iterator();
    while (it.hasNext()) {
        DefFunctionSymbol f = (DefFunctionSymbol)it.next();
        if (f.getSignatureClass() == Symbol.MAINSIG) {
        needed.add(f);
        }
    }
    needed = obl.getDependencies(needed);
    Set<DefFunctionSymbol> needed2 = obl.getDependencies(obl.mainFunctions);
    it = obl.defs.iterator();
        boolean changed = false;
    while (it.hasNext()) {
        DefFunctionSymbol f = (DefFunctionSymbol)it.next();
        if (!needed.contains(f)) {
        obl.ignoreIdentity.remove(f);
                delFuncs.add(f);
                changed = true;
        it.remove();
        }
        if (!needed2.contains(f) && f.getSignatureClass() == Symbol.DEFAULTSIG && !obl.isProjection(f)) {
        obl.deleteFunction(f);
                delFuncs.add(f);
                changed = true;
        }
    }
        if (!changed) {
            return null;
        }
        this.setProof(new DeleteUnneededFunctionsProof(oobl,delFuncs,obl));
        return obl;
    }

}
