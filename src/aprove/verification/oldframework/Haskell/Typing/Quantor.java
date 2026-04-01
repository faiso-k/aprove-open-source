package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.input.Generated.haskell.node.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * the quantor is the all-quantor in a type schema
 * and so it is a set of HaskellSym's
 */
public class Quantor extends HashSet<HaskellSym> implements HaskellObject {
    @Override
    public HaskellObject setToken(Token tok){ return this; }
    @Override
    public Token getToken(){ return null; }
    @Override
    public HaskellObject transferToken(HaskellObject a){ return a; };
    @Override
    public HaskellObject setTypeTerm(HaskellType typeTerm){ return this; }
    @Override
    public HaskellType getTypeTerm(){ return null; }

    public Quantor(){
        super();
    }

    public Quantor(Set<HaskellSym> syms){
        super(syms);
    }

    @Override
    public Object deepcopy(){
        return Copy.deepCol(this);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        if (hv.guardQuantor(this)){
            Set<HaskellSym> syms = new HashSet<HaskellSym>(this);
            this.clear();
            for (HaskellSym sym : syms){
                this.add(hv.walk(sym,hv));
            }
        }
        return hv.caseQuantor(this);
    }

    @Override
    public HaskellObject hoCopy(HaskellObject ho){
        return ho.setTypeTerm(Copy.deep(this.getTypeTerm()));
    }

    public int appendExport(int priority,Export_Util eu,StringBuffer t){
        return priority;
    }

}
