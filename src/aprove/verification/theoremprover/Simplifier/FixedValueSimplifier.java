package aprove.verification.theoremprover.Simplifier;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

@NoParams
public class FixedValueSimplifier extends BasicFixedValueSimplifier {

    public FixedValueSimplifier(){
        super("Fixed Value Simplifier","FVT","Fixed Value Transfortmation");
    }

    public FixedValueSimplifier(String pName,String psName,String plName) {
        super(pName,psName,plName);
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation oobl) {
        this.obl = oobl.shallowcopy();
        this.resetfvtInfo();
        this.fixedValueTransformation();
        Vector<Rule> vor = this.getfvtInfo();
        if (vor.isEmpty()) {
            return null;
        }
        this.setProof(new FixedValueProof(oobl,vor,this.obl));
        this.resetfvtInfo();
        return this.obl;
    }

    /* Fixed-Value-Transformation */

    /** Performes a fixed-value-transformation for every defining function
     *  in this.defs (if possible) and changes as much rules as possible
     *  to use the new functions.
     */
    public void fixedValueTransformation() {
    SimplifierProcessor.log.log(Level.FINER, "Simplifier: Performing fixed value transformation.\n");
    Vector fifo = new Vector(this.obl.defs);
    Hashtable origin = new Hashtable();
    Iterator it = fifo.iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        origin.put(fsym, fsym);
    }
    while (!fifo.isEmpty()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)fifo.remove(0);
        DefFunctionSymbol fnsym = this.fixedValueTransformation(fsym, origin);
        if (fnsym != null) {
        origin.put(fnsym, origin.get(fsym));
        fifo.add(fnsym);
        }
    }
    }

}
