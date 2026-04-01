package aprove.input.Programs.ipad;

import java.util.*;

import aprove.input.Generated.ipad.node.*;
import aprove.input.Programs.Predef.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

/** Treewalker that implements the second pass of
 *  the AST conversion.
 *  <p>
 *  This pass picks up all constructors and functions and adds the former to the
 *  corresponding sort.
 *  <p>
 *  Also, the defining rules for the equal_* functions
 *  are created for all possible constructor combinations.
 * @author Christian Haselbach
 * @version $Id$
 */

class SymbPass extends Pass {
    private Sort curstr;
    private int varcount;
    private Sort cursort;
    private TypeDefinition curTypeDef;
    private SyntacticFunctionSymbol curfun;
    private List<AlgebraTerm> curfunTyArgs;
    private ProcHead curProcHead;
    //private ConstructorSymbol curfun;
    private Set usedFunctNames;
    private AlgebraTerm curTy; // current type term

    @Override
    public void inStart(final Start node) {
    this.usedFunctNames = new HashSet();
    }

    @Override
    public void outStart(final Start node) {
        this.tyMakeWitnessTerms();
    this.witnessTerms = this.makeWitnessTerms();
        this.witnessTerms.put("bool",
            AlgebraFunctionApplication.create(this.prog.getFunctionSymbol("true")));
    }

    @Override
    public void caseAIdcomma(final AIdcomma node) {
    this.checkandadd(node.getType());
    }

    @Override
    public void caseAIdlist(final AIdlist node) {
    if (node.getIdcomma() != null) {
            final Iterator it = node.getIdcomma().iterator();
            while (it.hasNext()) {
                ((AIdcomma) it.next()).apply(this);
            }
        }
        this.checkandadd(node.getType());
    }

    @Override
    public void inAStruct(final AStruct node) {
        final String name = this.chop(node.getStructname());
        this.curTypeDef = this.typeContext.getTypeDef(name);
    this.curstr = this.prog.getSort(name);
    }

    @Override
    public void outAStruct(final AStruct node) {
    final Iterator c_it1 = this.curstr.getConstructorSymbols().iterator();
        while (c_it1.hasNext()) {
            final ConstructorSymbol csym1 = (ConstructorSymbol) c_it1.next();
            final DefFunctionSymbol fisa =
                this.prog.getPredefFunctionSymbol("isa_" + csym1.getName());
            csym1.setIsa(fisa);
            final Iterator c_it2 =
                this.curstr.getConstructorSymbols().iterator();
            while (c_it2.hasNext()) {
                final ConstructorSymbol csym2 =
                    (ConstructorSymbol) c_it2.next();
                this.varcount = 0;
                Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
                final Iterator s_it = csym2.getArgSorts().iterator();
                while (s_it.hasNext()) {
                    args.add(this.nextVar((Sort) s_it.next()));
                }
                AlgebraTerm left = AlgebraFunctionApplication.create(csym2, args);
                args = new Vector<AlgebraTerm>();
                args.add(left);
                left = AlgebraFunctionApplication.create(fisa, args);
                final AlgebraTerm right =
                    ConstructorApp.create(this.prog.getConstructorSymbol(csym1.equals(csym2)
                        ? "true" : "false"));
                this.prog.addRule(fisa, Rule.create(left, right));
            }
        }
    }

    @Override
    public void caseAParam(final AParam node) {
        final String name = this.chop(node.getId());
    node.getType().apply(this);
        final VariableSymbol sym =
            this.curProcHead.addVar(name, this.curTy, this.cursort,
                node.getVar() == null ? ProcHead.CALLBYVALUE
                    : ProcHead.CALLBYREF);
        if (sym == null) {
       this.addParseError(node.getId(), "variable ''" + name
                + "'' is multiple defined");
        }

    }

    @Override
    public void caseAType(final AType node) {
    final TId id = node.getId();
        final String name = this.chop(id);
        this.cursort = this.prog.getSort(name);
        this.curTy = this.getDeclaredType(name, node.getId());
    }

    @Override
    public void caseAFunct(final AFunct node) {
    final String fname = this.chop(node.getFunctname());
        if (!this.usedFunctNames.add(fname)) {
            this.addParseError(node.getFunctname(), "Multiple definition of ''"
                + fname + "''");
            return;
        }
        if (PredefFunctionSymbols.isPredefinedFunction(fname)) {
            this.addParseError(node.getFunctname(),
                "A function with the name ''" + fname + "'' is predefined");
        }
        this.curProcHead = new ProcHead(fname);
        final PTypevoid type = node.getTypevoid();
        if (type instanceof ATypeTypevoid) {
            final AType tmptoken =
                (AType) ((ATypeTypevoid) node.getTypevoid()).getType();
            final String name = this.chop(tmptoken.getId());
            final Sort s = this.prog.getSort(name);
            final AlgebraTerm ct = this.getDeclaredType(name,tmptoken.getId());         if (s == null) {
        this.addParseError(tmptoken.getId(), "unknown type");
            }
            this.curProcHead.setSort(s);
            this.curProcHead.setRetTy(ct);
        } else {
            this.curProcHead.setSort(null);
            this.curProcHead.setRetTy(null);
        }
        if (node.getParamlist() != null) {
            node.getParamlist().apply(this);
            // for every cbr-variable add a corresponding function-symbol
            final Iterator var_it = this.curProcHead.getVars().iterator();
            final Iterator ty_it = this.curProcHead.getFunArgTys().iterator();
            while (var_it.hasNext()) {
                final VariableSymbol argsym = (VariableSymbol) var_it.next();
                final AlgebraTerm curRetTy = (AlgebraTerm) ty_it.next();
                if (this.curProcHead.isCallByReferenceVarSym(argsym)) {
                    final DefFunctionSymbol def =
                        DefFunctionSymbol.create(
                            fname + "_" + argsym.getName(), new Vector<Sort>(
                                this.curProcHead.getFunArgSorts()),
                            argsym.getSort());
                    try {
                        this.prog.addDefFunctionSymbol(def);
                        this.prog.setFunctionSignature(def, Symbol.MAINSIG);
                        final AlgebraTerm cty =
                            TypeTools.function(this.curProcHead.getFunArgTys(),
                                curRetTy);
                        this.typeContext.setSingleTypeOf(def,
                            TypeTools.autoQuan(cty));
                    } catch (final Exception e) {
                        this.addParseError(node.getFunctname(),
                            "symbol redefined");
                    }
                }
            }
        }
        // if function has non-void return-type add a corresponding
        // function-symbol
        final Sort returnSort = this.curProcHead.getSort();
        final AlgebraTerm curRetTy = this.curProcHead.getRetTy();
        if (returnSort != null) {
            final DefFunctionSymbol def =
                DefFunctionSymbol.create(fname, new Vector<Sort>(
                    this.curProcHead.getFunArgSorts()), returnSort);
            final AlgebraTerm cty =
                TypeTools.function(this.curProcHead.getFunArgTys(), curRetTy);
            this.typeContext.setSingleTypeOf(def, TypeTools.autoQuan(cty));
            try {
                this.prog.addDefFunctionSymbol(def);
                this.prog.setFunctionSignature(def, Symbol.MAINSIG);
            } catch (final Exception e) {
                this.addParseError(node.getFunctname(), "symbol redefined");
            }
        }
        if (this.curProcHead.getRefVars().isEmpty() && returnSort == null) {
            this.addParseError(
                node.getFunctname(),
                "this is a useless function since it has neither a return value nor has it cbr-variables");
        }
        this.procHeads.put(fname, this.curProcHead);
    }

    @Override
    public void caseAConstr(final AConstr node) {
        final Token ret = node.getReturn();
    final String retName = this.chop(ret);
        final Sort s = this.prog.getSort(retName);
        final AlgebraTerm retTy = this.getDeclaredType(retName, ret);
        if (retTy == null) {
            return;
        }
        if (!this.checkTypes(retTy, this.curTypeDef.getDefTerm(), ret)) {
            return;
        }
        if (!this.checkdeclared(s, node.getReturn())) {
            return;
        }
        if (!this.checksorts(this.curstr, s, node.getReturn())) {
            return;
        }
        final ConstructorSymbol c =
            ConstructorSymbol.create(this.chop(node.getCons()), new Vector<Sort>(),
                s);
        this.curstr.addConstructorSymbol(c);
        try {
            this.prog.addConstructorSymbol(c);
        } catch (final ProgramException e) {
            this.addParseError(node.getCons(), "redeclaration of symbol ''"
                + this.chop(node.getCons()) + "''");
            return;
        }
        this.curfun = c;
        this.curfunTyArgs = new Vector<AlgebraTerm>();
        if (node.getIdlist() != null) {
            node.getIdlist().apply(this);
        }
        final AlgebraTerm ct =
            TypeTools.function(this.curfunTyArgs, this.curTypeDef.getDefTerm());
        this.curTypeDef.setSingleTypeOf(this.curfun, TypeTools.autoQuan(ct));
        this.makeEqualRules(node, s);
    }

    private void makeEqualRules(final AConstr node, final Sort s) {

    final DefFunctionSymbol feq =
            this.prog.getPredefFunctionSymbol("equal_" + s.getName());

    final DefFunctionSymbol fand = this.prog.getPredefFunctionSymbol("and");
        for (int i = 0; i < s.getConstructorSymbols().size(); i++) {
            final ConstructorSymbol c = s.getConstructorSymbol(i);
            if (c == this.curfun) {
                this.varcount = 0;
                final Vector<AlgebraTerm> a = new Vector<AlgebraTerm>();
                final Vector<AlgebraTerm> b = new Vector<AlgebraTerm>();
                AlgebraTerm r =
                    ConstructorApp.create(this.prog.getConstructorSymbol("true"));
                for (int j = 0; j < c.getArity(); j++) {
                    final Sort as = c.getArgSort(j);
                    final AlgebraTerm x1 = this.nextVar(as);
                    final AlgebraTerm x2 = this.nextVar(as);
                    a.add(x1);
                    b.add(x2);
                    final AlgebraTerm[] args2 = { x1, x2 };
                    final AlgebraTerm t =
                        DefFunctionApp.create(
                            this.prog.getPredefFunctionSymbol("equal_"
                                + as.getName()), args2);
                    if (j > 0) {
                        args2[0] = t;
                        args2[1] = r;
                        try {
                            this.prog.activatePredefFunctionSymbol(fand.getName());
                        } catch (final ProgramException e) {
                            if (fand != this.prog.getDefFunctionSymbol("&&")) {
                                this.addParseError(node.getCons(),
                                    "predefined and conflicts with and as defined by user");
                            }
                        }
                        r = DefFunctionApp.create(fand, args2);
                    } else {
                        r = t;
                    }
                }
                final AlgebraTerm[] args2 =
                    { ConstructorApp.create(c, a), ConstructorApp.create(c, b) };
                final AlgebraTerm l = DefFunctionApp.create(feq, args2);
                this.prog.addRule(feq, Rule.create(l, r));
            } else {
                this.varcount = 0;
                final Vector<AlgebraTerm> l1 = new Vector<AlgebraTerm>();
                final Vector<AlgebraTerm> l2 = new Vector<AlgebraTerm>();
                final Vector<AlgebraTerm> aa = new Vector<AlgebraTerm>();
                final Vector<AlgebraTerm> bb = new Vector<AlgebraTerm>();
                for (int j = 0; j < c.getArity(); j++) {
                    aa.add(this.nextVar(c.getArgSort(j)));
                }
                final AlgebraTerm a = ConstructorApp.create(c, aa);
                l1.add(a);
                for (int j = 0; j < this.curfun.getArity(); j++) {
                    bb.add(this.nextVar(this.curfun.getArgSort(j)));
                }
                final AlgebraTerm b =
                    ConstructorApp.create((ConstructorSymbol) this.curfun, bb);
                l1.add(b);
                l2.add(b);
                l2.add(a);
                this.prog.addRule(
                    feq,
                    Rule.create(
                        DefFunctionApp.create(feq, l1),
                        ConstructorApp.create(this.prog.getConstructorSymbol("false"))));
                this.prog.addRule(
                    feq,
                    Rule.create(
                        DefFunctionApp.create(feq, l2),
                        ConstructorApp.create(this.prog.getConstructorSymbol("false"))));
            }
        }
    }

    private AlgebraTerm nextVar(final Sort s) {
    this.varcount++;
        return AlgebraVariable.create(VariableSymbol.create("x"
            + Integer.valueOf(this.varcount).toString(), s));
    }

    private void checkandadd(final Token t) {
        final String name = this.chop(t);
    final AlgebraTerm ty = this.getDeclaredType(name, t);
        if (ty != null) {
            this.curfunTyArgs.add(ty);
        }
        final Sort s = this.prog.getSort(name);
        if (this.checkdeclared(s, t)) {
            this.curfun.addArgSort(s);
        }
    }

    /** if sorts are obsolete, remove this method
     */
    protected Hashtable makeWitnessTerms() {
    final Hashtable wterms = new Hashtable();
        final Vector<Sort> unassigned = new Vector<Sort>();
        Iterator it = this.sorttoken.keySet().iterator();
        while (it.hasNext()) {
            final String name = (String) it.next();
            unassigned.add(this.prog.getSort(name));
        }
        boolean changed = true;
        while (changed) {
            changed = false;
            it = unassigned.iterator();
            while (it.hasNext()) {
                final Sort s = (Sort) it.next();

                AlgebraTerm wt =
                    this.typeContext.getTypeDef(s.getName()).getWitnessTerm();
                if (wt == null) {
                    wt = SymbPass.makeWitnessTerm(s, wterms);
                }

                if (wt != null) {
                    wterms.put(s.getName(), wt);
                    it.remove();
                    changed = true;
                }
            }
        }
        if (!unassigned.isEmpty()) {
            final Sort s = unassigned.get(0);
            final Token t = (Token) this.sorttoken.get(s.getName());
            this.addParseError(t, "Structure " + s.getName() + " is empty.");
            return null;
        }
        return wterms;
    }

    /** if sorts are obsolete, remove this method
     */
    protected static AlgebraTerm makeWitnessTerm(final Sort s, final Hashtable wterms) {
    final Iterator it = s.getConstructorSymbols().iterator();
        while (it.hasNext()) {
            final ConstructorSymbol cons = (ConstructorSymbol) it.next();
            final AlgebraTerm wt = SymbPass.makeWitnessTerm(cons, wterms);
            if (wt != null) {
                return wt;
            }
        }
        return null;
    }

    /** if sorts are obsolete, remove this method
     */
    protected static AlgebraTerm makeWitnessTerm(final ConstructorSymbol cons, final Hashtable wterms) {
    final Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        final Iterator it = cons.getArgSorts().iterator();
        while (it.hasNext()) {
            final Sort s = (Sort) it.next();
            final AlgebraTerm wt = (AlgebraTerm) wterms.get(s.getName());
            if (wt == null) {
                return null;
            }
            args.add(wt.shallowcopy());
        }
        return AlgebraFunctionApplication.create(cons, args);
    }


    protected void tyMakeWitnessTerms() {
        final Vector unassigned = new Vector(this.typeContext.getTypeDefs());
        boolean changed = true;
        while (changed) {
            changed = false;
            final Iterator it = unassigned.iterator();
            while (it.hasNext()) {
                final TypeDefinition td = (TypeDefinition) it.next();
                if (td.getWitnessTerm() == null) {
                    final AlgebraTerm wt = this.tyMakeWitnessTerm(td);
                    if (wt != null) {
                        td.setWitnessTerm(wt);
                        it.remove();
                        changed = true;
                    }
                } else {
                    it.remove();
                }
            }
        }
        if (!unassigned.isEmpty()) {
            final TypeDefinition td = (TypeDefinition) unassigned.get(0);
            final Token t =
                (Token) this.sorttoken.get(td.getTypeCons().getName());
            this.addParseError(t, "Structure " + td.getTypeCons().getName()
                + " is empty.");
            return;
        }
    }

    protected AlgebraTerm tyMakeWitnessTerm(final TypeDefinition td) {
    final Iterator it = td.getDeclaredSymbols().iterator();
        while (it.hasNext()) {
            final ConstructorSymbol cons = (ConstructorSymbol) it.next();
            final AlgebraTerm wt = this.tyMakeWitnessTerm(cons, td.getSingleTypeOf(cons));
            if (wt != null) {
                return wt;
            }
        }
        return null;
    }

    protected AlgebraTerm tyMakeWitnessTerm(final ConstructorSymbol cons,final Type consType) {
    final Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        final AlgebraTerm cty = consType.getTypeMatrix();
        final Iterator it = TypeTools.getFunctionArgs(cty).iterator();
        while (it.hasNext()) {
            final ConstructorSymbol atc =
                (ConstructorSymbol) ((AlgebraTerm) it.next()).getSymbol();
            final AlgebraTerm wt = this.typeContext.getTypeDefOf(atc).getWitnessTerm();
            if (wt == null) {
                return null;
            }
            args.add(wt.shallowcopy());
        }
        return AlgebraFunctionApplication.create(cons, args);
    }

}
