package aprove.input.Programs.fp;

import java.util.*;

import aprove.input.Generated.fp.node.*;
import aprove.input.Programs.Predef.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** Treewalker that implements the second pass of
 *  the AST conversion.
 *  <p>
 *  This pass picks up all constructors and defined
 *  functions and adds the former to the
 *  corresponding sort. At the end a nonemptiness
 *  check is done for all sorts.
 *  <p>
 *  Also, the defining rules for the equal_* functions
 *  are created for all possible constructor combinations.
 *  The witness-terms are created here.
 *
 * @author Peter Schneider-Kamp, Christian Haselbach
 * @version $Id$
 */

class Pass2 extends Pass {

    private Sort curstr;
    private TypeDefinition curTypeDef;
    private SyntacticFunctionSymbol curfun;
    private List<AlgebraTerm> curfunTyArgs;
    private int varcount;

    @Override
    public void inStart(Start node) {
    super.inStart(node);
    }

    @Override
    public void outStart(Start node) {
    this.makeWitnessTerms();
    this.tyMakeWitnessTerms();
    }

    @Override
    public void inAStruct(AStruct node) {
    String name = this.chop(node.getStructname());
    this.curstr = this.prog.getSort(name);
    this.curTypeDef = this.typeContext.getTypeDef(name);
    }

    protected void makeWitnessTerms() {
    Vector<Sort> unassigned = new Vector<Sort>();
    Iterator it = this.sorttoken.keySet().iterator();
    while (it.hasNext()) {
        String name = (String)it.next();
        Sort sort = this.prog.getSort(name);
        if (sort.getWitnessTerm() == null) {
            unassigned.add(this.prog.getSort(name));
        }
    }
    boolean changed = true;
    while (changed) {
        changed = false;
        it = unassigned.iterator();
        while (it.hasNext()) {
        Sort s = (Sort)it.next();
        AlgebraTerm wt = Pass2.makeWitnessTerm(s);
        if (wt != null) {
            s.setWitnessTerm(wt);
            it.remove();
            changed = true;
        }
        }
    }
    if (!unassigned.isEmpty()) {
        Sort s = (Sort)unassigned.get(0);
        Token t = (Token)this.sorttoken.get(s.getName());
        this.addParseError(t, "Structure "+s.getName()+" is empty.");
    }
    }

    protected static AlgebraTerm makeWitnessTerm(Sort s) {
    Iterator it = s.getConstructorSymbols().iterator();
    while (it.hasNext()) {
        ConstructorSymbol cons = (ConstructorSymbol)it.next();
        AlgebraTerm wt = Pass2.makeWitnessTerm(cons);
        if (wt != null) {
        return wt;
        }
    }
    return null;
    }

    protected static AlgebraTerm makeWitnessTerm(ConstructorSymbol cons) {
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    Iterator it = cons.getArgSorts().iterator();
    while (it.hasNext()) {
        Sort s = (Sort)it.next();
        AlgebraTerm wt = s.getWitnessTerm();
        if (wt == null) {
        return null;
        }
        args.add(wt.shallowcopy());
    }
    return AlgebraFunctionApplication.create(cons, args);
    }

        protected void tyMakeWitnessTerms() {
    Hashtable wterms = new Hashtable();
    Vector unassigned = new Vector(this.typeContext.getTypeDefs());
    boolean changed = true;
    while (changed) {
        changed = false;
        Iterator it = unassigned.iterator();
        while (it.hasNext()) {
        TypeDefinition td = (TypeDefinition)it.next();
        if (td.getWitnessTerm() != null) {
            it.remove();
            continue;
        }
        AlgebraTerm wt = this.tyMakeWitnessTerm(td);
        if (wt != null) {
            td.setWitnessTerm(wt);
            it.remove();
            changed = true;
        }
        }
    }
    if (!unassigned.isEmpty()) {
        TypeDefinition td = (TypeDefinition) unassigned.get(0);
        Token t = (Token)this.sorttoken.get(td.getTypeCons().getName());
        this.addParseError(t, "Structure "+td.getTypeCons().getName()+" is empty.");
        return;
    }
    }

    protected AlgebraTerm tyMakeWitnessTerm(TypeDefinition td) {
    Iterator it = td.getDeclaredSymbols().iterator();
    while (it.hasNext()) {
        ConstructorSymbol cons = (ConstructorSymbol)it.next();
        AlgebraTerm wt = this.tyMakeWitnessTerm(cons,td.getSingleTypeOf(cons));
        if (wt != null) {
        return wt;
        }
    }
    return null;
    }

    protected AlgebraTerm tyMakeWitnessTerm(ConstructorSymbol cons,Type consType) {
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    AlgebraTerm cty = consType.getTypeMatrix();
    Iterator it = TypeTools.getFunctionArgs(cty).iterator();
    while (it.hasNext()) {
        ConstructorSymbol atc = (ConstructorSymbol)((AlgebraTerm)it.next()).getSymbol();
        AlgebraTerm wt = this.typeContext.getTypeDefOf(atc).getWitnessTerm();
        if (wt == null) {
        return null;
        }
        args.add(wt.shallowcopy());
    }
    return AlgebraFunctionApplication.create(cons, args);
    }

    @Override
    public void outAStruct(AStruct node) {
    Iterator c_it1 = this.curstr.getConstructorSymbols().iterator();
    while (c_it1.hasNext()) {
        ConstructorSymbol csym1 = (ConstructorSymbol)c_it1.next();
        DefFunctionSymbol fisa = this.prog.getPredefFunctionSymbol("isa_"+csym1.getName());
        csym1.setIsa(fisa);
        Iterator c_it2 = this.curstr.getConstructorSymbols().iterator();
        while (c_it2.hasNext()) {
        ConstructorSymbol csym2 = (ConstructorSymbol)c_it2.next();
        this.varcount = 0;
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        Iterator s_it = csym2.getArgSorts().iterator();
        while (s_it.hasNext()) {
            args.add(this.nextVar((Sort)s_it.next()));
        }
        AlgebraTerm left = AlgebraFunctionApplication.create(csym2, args);
        args = new Vector<AlgebraTerm>();
        args.add(left);
        left = AlgebraFunctionApplication.create(fisa, args);
        AlgebraTerm right = ConstructorApp.create(this.prog.getConstructorSymbol(csym1.equals(csym2) ? "true" : "false"));
        this.prog.addRule(fisa, Rule.create(left, right));
        }
    }
    }

    @Override
    public void caseAFunct(AFunct node) {
        Token ret = node.getReturn();
        String retName = this.chop(ret);
    Sort s = this.prog.getSort(retName);
    if (!this.chop(node.getColon()).equals(":")) {
        this.addParseError(node.getColon(), "'':'' expected");
    }

    AlgebraTerm retTy = this.getDeclaredType(retName,ret);
    if (retTy == null) { return; }
    if (!this.checkdeclared(s, node.getReturn())) {return;}

    String name = this.chop(node.getFunctname());

    if (PredefFunctionSymbols.isPredefinedFunction(name)) {
        this.addParseError(node.getFunctname(), "A function with name ''"+name+"'' is predefined. Please choose a different name.");
    }

    DefFunctionSymbol f = DefFunctionSymbol.create(name,new Vector<Sort>(),s);

    // getting the argument sorts/types
    this.curfun = f;
    this.curfunTyArgs = new Vector<AlgebraTerm>();
    if (node.getIdlist() != null) {node.getIdlist().apply(this);}
    this.usedNames.add(name);

    try {
        this.prog.addDefFunctionSymbol(f);
        f.setSignatureClass(node.getPrivate() == null ? Symbol.MAINSIG : Symbol.DEFAULTSIG);
    }
    catch (ProgramException e) {
        this.redeclaration(node.getFunctname());
        return;
    }

    Type ct = TypeTools.autoQuan(TypeTools.function(this.curfunTyArgs,retTy));
    this.typeContext.setSingleTypeOf(this.curfun,ct);
    }

    public static Triple<Integer,Integer,Boolean> readOptions(Token id, POptions options, SyntacticFunctionSymbol fsym, Pass pass) {
    Integer level = null;
    String fixity = null;

    LinkedList<PEid> eidOptions = new LinkedList<PEid>();

    // check whether this is a infix or ac option (others are not defined up to now)
    boolean hasOptions = false;
    if (options instanceof AKeyOptions) {
        AKeyOptions keyOption = (AKeyOptions)options;
        fixity = keyOption.getOptionkey().toString().trim();
        eidOptions.addAll(keyOption.getOptions1());
        eidOptions.addAll(keyOption.getOptions2());
        hasOptions = true;
    }
    else if (options instanceof ANoKeyOptions) {
        ANoKeyOptions noOption = (ANoKeyOptions)options;
        eidOptions.addAll(noOption.getEid());
        hasOptions = true;
    }

    // Read the options that have been declared.
    if (hasOptions) {

        if (eidOptions.size() > 1) {
        pass.addParseError(id, "faulty function/constructor-definition");
        }
        Iterator it = eidOptions.iterator();
        while (it.hasNext()) {
        PEid eid = (PEid)it.next();
        Token rid;
        if (eid instanceof AAppEid) {
            rid = ((AAppEid)eid).getId();
        }
        else {
            rid = ((ANoappEid)eid).getNoappid();
        }
        String opt = pass.chop(rid);
        Integer l = null;
        try {
            l = Integer.valueOf(opt);
        }
        catch (Exception e) {
            l = null;
        }
        if (!( l != null || opt.equals("infixl") || opt.equals("infixr") || opt.equals("infix") || opt.equals("ac"))) {
            pass.addParseError(id, "faulty function-definition");
        }
        else {
            if (l != null) {
            if (l.intValue() > 9 || l.intValue() < 0) {
                pass.addParseError(rid, "precedence must be between 0 and 9");
            }
            if (level != null) {
                pass.addParseError(rid, "multiple definition of precedence");
            }
            level = l;
            }
            else {
            if (fixity != null) {
                pass.addParseError(id, "multiple definition of fixity");
            }
            fixity = opt;
            }
        }
        }
    }

    boolean usedDefaults = false;

    // Use default-values if necessary.
    if (fixity == null) {
        usedDefaults = true;
        fixity = "infixl";
    }
    if (level == null) {
        level = Integer.valueOf(9);
    }
    else {
        usedDefaults = false;
    }

    int i;
    if (fixity.equals("infix")) {
        i = SyntacticFunctionSymbol.INFIX;
    }
    else if (fixity.equals("infixl")) {
        i = SyntacticFunctionSymbol.INFIXL;
    }
    else if (fixity.equals("infixr")) {
        i = SyntacticFunctionSymbol.INFIXR;
    }
    else {
        i = SyntacticFunctionSymbol.NOTINFIX;
    }
    if (fsym != null) {
        fsym.setFixity(i, level.intValue());
    }
    return new Triple<Integer,Integer,Boolean>(i,level, usedDefaults);
    }

    @Override
    public void caseAOpdef(AOpdef node) {
        Token ret = node.getReturn();
        String retName = this.chop(ret);
    Sort s = this.prog.getSort(retName);
    if (!this.chop(node.getColon()).equals(":")) {
        this.addParseError(node.getColon(), "'':'' expected");
    }
    AlgebraTerm retTy = this.getDeclaredType(retName,ret);
    if (retTy == null) { return; }
    if (!this.checkdeclared(s, node.getReturn())) {
        return;
    }
    String name = this.chop(node.getOpname());
    if (name.startsWith("==")) {
        this.addParseError(node.getOpname(), "infix-function-names starting with ''=='' are preserved");
        return;
    }
    this.usedNames.add(name);
    DefFunctionSymbol f = DefFunctionSymbol.create(name, new Vector<Sort>(),s);
    f.setSignatureClass(Symbol.MAINSIG);

    try {
        this.prog.addDefFunctionSymbol(f);
    }
    catch (ProgramException e) {
        this.redeclaration(node.getOpname());
        return;
    }

    this.curfun = f;
    this.curfunTyArgs = new Vector<AlgebraTerm>();
    if (node.getIdlist() != null) {
        node.getIdlist().apply(this);
    }
    if (f.getArity() != 2) {
        this.addParseError(node.getOpname(), "infix-function must have arity 2");
    }
    Pass2.readOptions(node.getOpname(), node.getOptions(), f, this);
    Type ct = TypeTools.autoQuan(TypeTools.function(this.curfunTyArgs,retTy));
    this.typeContext.setSingleTypeOf(this.curfun,ct);


    // Handling of the following predefined Integer infix functions
    List<String> intPredefs = Arrays.asList("+", "-", "*", "/", "<", "<=", ">", ">=", "%");
    boolean isIntOperator = this.containsInts && intPredefs.contains(name);

    if(isIntOperator) {
        this.addParseError(node.getOpname(), "infix-function ''"+name+"'' working on Integers is predefined.");
    }
    }

    @Override
    public void inASelidcomma(ASelidcomma node) {
    this.checkandadd(node.getSort());
    }

    @Override
    public void outASelidlist(ASelidlist node) {
    this.checkandadd(node.getSort());
    }

    @Override
    public void inAIdcomma(AIdcomma node) {
    this.checkandadd(node.getId());
    }

    @Override
    public void outAIdlist(AIdlist node) {
    this.checkandadd(node.getId());
    }


    @Override
    public void caseAInfixconstr(AInfixconstr node) {
    ConstructorSymbol c = this.makeconstr((Token)node.getCons(), (ASelidlist)node.getSelidlist(), node.getReturn(), node.getColon());
    Pass2.readOptions(node.getCons(), node.getOptions(), c, this);
    }

    @Override
    public void caseAConstr(AConstr node) {
    Node n = node.getCons();
    Token tcons = null;
    if (n instanceof ANoappEid) {
        tcons = ((ANoappEid)n).getNoappid();
    }
    else {
        tcons = ((AAppEid)n).getId();
    }
    this.makeconstr(tcons, (ASelidlist)node.getSelidlist(), node.getReturn(), node.getColon());
    }

    public ConstructorSymbol makeconstr(Token cons, ASelidlist idlist, Token ret, Token colon) {
    if (!this.chop(colon).equals(":")) {
        this.addParseError(colon, "'':'' expected");
    }
    String retName = this.chop(ret);
    Sort s = this.prog.getSort(retName);
    AlgebraTerm retTy = this.getDeclaredType(retName,ret);
    if (retTy == null) { return null; }
    if (!this.checkType(retTy,this.curTypeDef.getDefTerm(),ret)) { return null; }
    if (!this.checkdeclared(s, ret)) {
        return null;
    }
    if (!this.checksorts(this.curstr, s, ret)) {
        return null;
    }
    String name = this.chop(cons);

    this.usedNames.add(name);
    ConstructorSymbol c = ConstructorSymbol.create(name,new Vector<Sort>(),s);
    this.curstr.addConstructorSymbol(c);
    try {this.prog.addConstructorSymbol(c);}
    catch (ProgramException e) {
        this.redeclaration(cons);
        return null;
    }


    this.curfun = c;
    this.curfunTyArgs = new Vector<AlgebraTerm>();
    if (idlist != null) {idlist.apply(this);}
    AlgebraTerm ct = TypeTools.function(this.curfunTyArgs,this.curTypeDef.getDefTerm());
    this.curTypeDef.setSingleTypeOf(this.curfun,TypeTools.autoQuan(ct));
    DefFunctionSymbol feq = this.prog.getPredefFunctionSymbol("equal_"+s.getName());
    DefFunctionSymbol fand = this.prog.getPredefFunctionSymbol("and");
    for (int i=0; i<s.getConstructorSymbols().size(); i++) {
        c = s.getConstructorSymbol(i);
        if (c == this.curfun) {
        this.varcount = 0;
        Vector<AlgebraTerm> a = new Vector<AlgebraTerm>();
        Vector<AlgebraTerm> b = new Vector<AlgebraTerm>();
        AlgebraTerm r = ConstructorApp.create(this.prog.getConstructorSymbol("true"));
        for (int j=0; j<c.getArity(); j++) {
            Sort as = c.getArgSort(j);
            AlgebraTerm x1 = this.nextVar(as);
            AlgebraTerm x2 = this.nextVar(as);
            a.add(x1);
            b.add(x2);
            AlgebraTerm[] args2 = { x1, x2 };
            AlgebraTerm t = DefFunctionApp.create(this.prog.getPredefFunctionSymbol("equal_"+as.getName()), args2);
            if (j > 0) {
            args2[0] = t;
            args2[1] = r;
            try {
                this.prog.activatePredefFunctionSymbol(fand.getName());
            } catch (ProgramException e) {
                if (fand != this.prog.getDefFunctionSymbol("&&")) {
                this.addParseError(cons, "predefined and conflicts with and as defined by user");
                }
            }
            r = DefFunctionApp.create(fand, args2);
            } else {
            r = t;
            }
        }
        AlgebraTerm[] args2 = { ConstructorApp.create(c, a), ConstructorApp.create(c, b) };
        AlgebraTerm l = DefFunctionApp.create(feq, args2);
        this.prog.addRule(feq, Rule.create(l, r));
        }
        else {
        this.varcount = 0;
        Vector<AlgebraTerm> l1 = new Vector<AlgebraTerm>();
        Vector<AlgebraTerm> l2 = new Vector<AlgebraTerm>();
        Vector<AlgebraTerm> aa = new Vector<AlgebraTerm>();
        Vector<AlgebraTerm> bb = new Vector<AlgebraTerm>();
        for (int j=0; j<c.getArity(); j++) {
            aa.add(this.nextVar(c.getArgSort(j)));
        }
        AlgebraTerm a = ConstructorApp.create(c, aa);
        l1.add(a);
        for (int j=0; j<this.curfun.getArity(); j++) {
            bb.add(this.nextVar(this.curfun.getArgSort(j)));
        }
        AlgebraTerm b = ConstructorApp.create((ConstructorSymbol)this.curfun, bb);
        l1.add(b);
        l2.add(b);
        l2.add(a);
        this.prog.addRule(feq, Rule.create(DefFunctionApp.create(feq, l1), ConstructorApp.create(this.prog.getConstructorSymbol("false"))));
        this.prog.addRule(feq, Rule.create(DefFunctionApp.create(feq, l2), ConstructorApp.create(this.prog.getConstructorSymbol("false"))));
        }
    }
    return c;
    }

    private AlgebraTerm nextVar(Sort s) {
    this.varcount++;
    return AlgebraVariable.create(VariableSymbol.create("x"+Integer.valueOf(this.varcount).toString(), s));
    }
    private void checkandadd(Token t) {
        String name = this.chop(t);
    AlgebraTerm ty = this.getDeclaredType(name,t);
    if (ty != null) {
        this.curfunTyArgs.add(ty);
    }
    Sort s = this.prog.getSort(name);
    if (this.checkdeclared(s, t)) {
        this.curfun.addArgSort(s);
    }
    }

}
