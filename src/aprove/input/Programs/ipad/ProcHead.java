package aprove.input.Programs.ipad;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Class to store informations about procedure-headers (e.g. parameters)
 *  @author Christian Haselbach
 *  @version $Id$
 */

class ProcHead {

    private String fname;
    private Vector<VariableSymbol> vars;
    private Hashtable vartypes;
    private Vector<Sort> funargsorts;
    private Vector<AlgebraTerm> funargtys;
    private Sort sort;
    private List<AlgebraTerm> args;
    private Hashtable vartable;
    private AlgebraTerm retTy; // return type term

    public final static int CALLBYVALUE = 0;
    public final static int CALLBYREF = 1;
    public final static int INTERNALVAR = 2;

    public ProcHead(String name) {
    this.fname = name;
    this.funargsorts = new Vector<Sort>();
    this.funargtys = new Vector<AlgebraTerm>();
    this.vartypes = new Hashtable();
    this.vars = new Vector<VariableSymbol>();
    this.vartable = new Hashtable();
    this.args = new Vector<AlgebraTerm>();
    this.sort = null;
    this.retTy = null;
    }

    public ProcHead copy() {
    ProcHead ph = new ProcHead(this.fname);
    Iterator it = this.vars.iterator();
    Iterator jt = this.funargtys.iterator();
    while (it.hasNext()) {
        VariableSymbol sym = (VariableSymbol)it.next();
        AlgebraTerm cty = (AlgebraTerm) jt.next();
        ph.addVar(sym.getName(),cty, sym.getSort(), ((Integer)this.vartypes.get(sym)).intValue());
    }
    ph.setSort(this.sort);
    ph.setRetTy(this.retTy);
    return ph;
    }

    public VariableSymbol addVar(String varname, AlgebraTerm tt, Sort sort, int mode) {
    VariableSymbol sym = VariableSymbol.create(varname, sort);
        if (this.vartable.containsKey(varname)) { return null; }
    this.vartable.put(varname, sym);
    this.vars.add(sym);
    this.args.add(AlgebraVariable.create(sym));
    this.funargsorts.add(sort);
    this.funargtys.add(tt);
    this.vartypes.put(sym, Integer.valueOf(mode));
    return sym;
    }

    public String getName() {
    return this.fname;
    }

    public Set<VariableSymbol> getValVars() {
    Set<VariableSymbol> vs = new HashSet<VariableSymbol>();
    Iterator it = this.vartypes.keySet().iterator();
    while (it.hasNext()) {
        VariableSymbol sym = (VariableSymbol)it.next();
        if (((Integer)this.vartypes.get(sym)).intValue()==ProcHead.CALLBYVALUE) {
        vs.add(sym);
        }
    }
    return vs;
    }

    public Set<VariableSymbol> getRefVars() {
    Set<VariableSymbol> vs = new HashSet<VariableSymbol>();
    Iterator it = this.vartypes.keySet().iterator();
    while (it.hasNext()) {
        VariableSymbol sym = (VariableSymbol)it.next();
        if (((Integer)this.vartypes.get(sym)).intValue()==ProcHead.CALLBYREF) {
        vs.add(sym);
        }
    }
    return vs;
    }

    public Vector<VariableSymbol> getVars() {
    return this.vars;
    }

    public Vector<Sort> getFunArgSorts() {
    return this.funargsorts;
    }

    public Vector<AlgebraTerm> getFunArgTys() {
    return this.funargtys;
    }

    public List<AlgebraTerm> getArgs() {
    return this.args;
    }

    public int getArity() {
    return this.args.size();
    }

    public Sort getArgSort(int i) {
    return (Sort)this.funargsorts.get(i);
    }

    public Sort getSort() {
    return this.sort;
    }

    public AlgebraTerm getRetTy() {
    return this.retTy;
    }

    public void setRetTy(AlgebraTerm retTy) {
    this.retTy = retTy;
    }

    public void setSort(Sort s) {
    this.sort = s;
    }

    public boolean isCallByValueArgument(int i) {
    return ((Integer)this.vartypes.get(this.vars.get(i))).intValue()==ProcHead.CALLBYVALUE;
    }

    public boolean isCallByReferenceArgument(int i) {
    return ((Integer)this.vartypes.get(this.vars.get(i))).intValue()==ProcHead.CALLBYREF;
    }

    public boolean isCallByReferenceVarSym(VariableSymbol varsym) {
    return ((Integer)this.vartypes.get(varsym)).intValue()==ProcHead.CALLBYREF;
    }

    public boolean isInternalVariable(int i) {
    return ((Integer)this.vartypes.get(this.vars.get(i))).intValue()==ProcHead.INTERNALVAR;
    }

    public VariableSymbol getVariableSymbol(String varname) {
    return (VariableSymbol)this.vartable.get(varname);
    }

    public AlgebraTerm getVariableSymbolType(String varname) {
        Iterator<AlgebraTerm> varIt = this.getArgs().iterator();
        Iterator<AlgebraTerm> varTypeIt = this.getFunArgTys().iterator();
        while (varIt.hasNext()) {
            AlgebraTerm var = varIt.next();
            AlgebraTerm varType = varTypeIt.next();
            if (var.getSymbol().getName().equals(varname)) {
                 return varType;
            }
        }
        return null;
    }

    public String getArgName(int i) {
    return this.vars.get(i).getName();
    }

    @Override
    public String toString() {
    String s = this.fname+"(";
    String t = "";
    Iterator it = this.vars.iterator();
    while (it.hasNext()) {
        VariableSymbol sym = (VariableSymbol)it.next();
        switch (((Integer)this.vartypes.get(sym)).intValue()) {
        case CALLBYVALUE:
            s += sym.getSort().getName()+" "+sym.getName()+", ";
            break;
        case CALLBYREF:
            s += "var "+sym.getSort().getName()+" "+sym.getName()+", ";
            break;
        case INTERNALVAR:
            t += sym.getSort().getName()+" "+sym.getName()+", ";
            break;
        }
    }
    return s+")"+t;
    }
}
