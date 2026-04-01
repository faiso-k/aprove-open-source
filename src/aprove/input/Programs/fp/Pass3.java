package aprove.input.Programs.fp;

import java.util.*;

import aprove.input.Generated.fp.node.*;
import aprove.input.Programs.Predef.*;
import aprove.input.Programs.Predef.IntegerPredef.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.*;

/** Treewalker that implements the third pass of
 *  the AST conversion.
 *  <p>
 *  This pass picks up all rules for the defined
 *  function. In a nutshell, this pass is a
 *  term parser.
 *  </p>
 * @version $Id$
 * @author Peter Schneider-Kamp, Christian Haselbach
 */

class Pass3 extends Pass {

    private DefFunctionSymbol curfun;
    private Token curfuntoken;
    private Stack<Sort> sorts;
    private Hashtable vars;
    private boolean lhs;
    private boolean visitedrootsymbol; /* A flag if the rootsymbol on the lhs has been visited. */
    private Stack<CondTerm> terms;
    private Stack<AlgebraTerm> lhsterms;
    private Set<AlgebraTerm> defpatterns; /* A set of terms wich represent the pattern of a defining equation. */
    private LinkedHashSet<Rule> curfunRules; /* A set of rules, collecting the rules for the DefFunctionSymbol curfun. Order is important, hence the LinkedHashSet */
    private ConstructorSymbol curconstr;
    private int selectorindex;
    private Vector<DefFunctionSymbol> curselectors;
    private Sort cursort;
    private Vector<CondTerm> letList;
    private Vector<AlgebraTerm> letTerms;
    private Stack letListStack;
    private Stack letTermsStack;
    private Hashtable letvars; /* Local vars introduced by let. */
    private Vector<String> forbiddenLetVars; /* variables which are currently not allowed (inside rhs of let) */
    private HashMap<VariableSymbol, CondTerm> letReplacements; /* collects the replacements which are to be made for let-expressions */
    private FreshNameGenerator varnamegen;

    private AlgebraTerm curleft; /* the current left hand side of a rule */



    private void pushdummyterm(Sort s) {
    ConstructorSymbol dummyconst = ConstructorSymbol.create(s.getName()+"dummy", new Vector<Sort>(), s);
    AlgebraTerm t = ConstructorApp.create(dummyconst);
    if (this.lhs) {
        this.lhsterms.add(t);
    }
    else {
        this.terms.add(CondTerm.create(t));
    }
    }

    private String getAVariableName(int i) {
    String s = null;
    switch (i % 6) {
        case 0:
        s = "x";
        break;
        case 1:
        s = "y";
        break;
        case 2:
        s = "z";
        break;
        case 3:
        s = "u";
        break;
        case 4:
        s = "v";
        break;
        case 5:
        s = "w";
        break;
    }
    return (i < 6) ? s : s+(i / 6);
    }

    @Override
    public void inStart(Start node) {
    this.sorts = new Stack<Sort>();
    this.vars = new Hashtable();
    this.terms = new Stack<CondTerm>();
    this.lhsterms = new Stack<AlgebraTerm>();
    this.defpatterns = new HashSet<AlgebraTerm>();
    this.curfunRules = new LinkedHashSet<Rule>();
    this.letList = null;
    this.letTerms = null;
    this.letListStack = new Stack();
    this.letTermsStack = new Stack();
    this.letvars = new Hashtable();
    this.forbiddenLetVars = new Vector<String>();
    this.letReplacements = new HashMap<VariableSymbol, CondTerm>();
   }

    @Override
    public void inAStruct(AStruct node) {
        String structName = this.chop(node.getStructname());
        if (structName.equals(Pass.FP_UNKNOWN_SORT.getName())) {
            this.addParseError(node.getStructname(), "Sorry, this structname is not allowed.");
        }
    this.cursort = this.prog.getSort(this.chop(node.getStructname()));
    }

    @Override
    public void inAInfixconstr(AInfixconstr node) {
    this.curconstr = this.prog.getConstructorSymbol(this.chop(node.getCons()));
    this.curselectors = new Vector<DefFunctionSymbol>();
    this.selectorindex = 0;
    }

    @Override
    public void inAConstr(AConstr node) {
    this.curconstr = this.prog.getConstructorSymbol(this.chop(node.getCons()));
    this.curselectors = new Vector<DefFunctionSymbol>();
    this.selectorindex = 0;
    }

    @Override
    public void outAConstr(AConstr node) {
    this.curconstr.setSelectors(this.curselectors);
    }

    @Override
    public void outAInfixconstr(AInfixconstr node) {
    this.curconstr.setSelectors(this.curselectors);
    }

    @Override
    public void caseASelidcomma(ASelidcomma node) {
    this.makeSelector((ASelector)node.getSelector());
    }

    @Override
    public void caseASelidlist(ASelidlist node) {
    if (node.getSelidcomma()!= null) {
        Iterator it = node.getSelidcomma().iterator();
        while (it.hasNext()) {
        ((ASelidcomma)it.next()).apply(this);
        }
    }
    this.makeSelector((ASelector)node.getSelector());
    }

    private void makeSelector(ASelector sel) {
    String name;
    if (sel!=null) {
        name = this.chop(sel.getName());
    }
    else {
        name = "@"+this.curconstr.getName()+"_"+this.selectorindex;
    }
    DefFunctionSymbol def = DefFunctionSymbol.create(name, new Vector<Sort>(), this.curconstr.getArgSort(this.selectorindex));
    def.addArgSort(this.curconstr.getSort());
    Type selType = this.typeContext.getSingleTypeOf(this.curconstr).createSelType(this.selectorindex);
        this.typeContext.setSingleTypeOf(def,selType);

    // selectors are terminating by construction
    def.setTermination(true);
    try {
        this.prog.addPredefFunctionSymbol(def);
        def.setSignatureClass(Symbol.SELECTORSIG);
        this.curselectors.add(def);
    }
    catch (Exception e) { }
    AlgebraTerm witness = this.curconstr.getArgSort(this.selectorindex).getWitnessTerm();
    Iterator it = this.curconstr.getSort().getConstructorSymbols().iterator();
    while (it.hasNext()) {
        ConstructorSymbol conssym = (ConstructorSymbol)it.next();
        List<AlgebraTerm> tl = new Vector<AlgebraTerm>();
        Iterator s_it = conssym.getArgSorts().iterator();
        int i=0;
        while (s_it.hasNext()) {
        Sort s = (Sort)s_it.next();
        tl.add(AlgebraVariable.create(VariableSymbol.create(this.getAVariableName(i++), s)));
        }
        List<AlgebraTerm> f = new Vector<AlgebraTerm> ();
        f.add(ConstructorApp.create(conssym, tl));
        AlgebraTerm tr;
        if (conssym.equals(this.curconstr)) {
        tr = tl.get(this.selectorindex);
        }
        else {
        tr = witness;
        }
        this.prog.addRule(Rule.create(AlgebraFunctionApplication.create(def, f), tr));
    }
    this.selectorindex++;
    }

    @Override
    public void inAFunct(AFunct node) {
    this.curfuntoken = node.getFunctname();
    this.curfun = this.prog.getDefFunctionSymbol(this.chop(this.curfuntoken));
    this.defpatterns.clear();
    this.curfunRules.clear();
    }

    @Override
    public void inAOpdef(AOpdef node) {
    this.curfuntoken = node.getOpname();
    this.curfun = this.prog.getDefFunctionSymbol(this.chop(this.curfuntoken));
    this.defpatterns.clear();
    this.curfunRules.clear();
    }

    @Override
    public void outAFunct(AFunct node) {
    this.outAFunctOrAOpdef();
    }

    @Override
    public void outAOpdef(AOpdef node) {
    this.outAFunctOrAOpdef();
    }

    public void outAFunctOrAOpdef() {

        // making the patterns disjunct
        LinkedHashSet<Rule> rules = PatternDisjunctor.makePatternsNonOverlapping(this.curfunRules, this.typeContext, this.containsInts);

        this.prog.addRules(rules);

        // Update defpatterns
        this.defpatterns.clear();
        for(Rule r : rules) {
            this.defpatterns.add(r.getLeft());
        }

    Set<AlgebraTerm> todo_terms = Program.checkApplicabilityByTerms(this.curfun, this.defpatterns, this.typeContext);

    // removing all cases where integers would have to be built from pred inside a succ and vice versa
    if (this.containsInts) {
        Iterator<AlgebraTerm> todoTerms_it = todo_terms.iterator();
        while (todoTerms_it.hasNext()) {
            AlgebraTerm todoTerm = todoTerms_it.next();
            if (!IntegerTools.containsOnlyValidIntegerTerms(todoTerm, this.typeContext)) {
                todoTerms_it.remove();
            }
        }
    }
    if (!todo_terms.isEmpty()) {
        this.addParseError(this.curfuntoken,
            "Function-definition is not complete. The following cases are missing: "+
            todo_terms);
    }
    }



    @Override
    public void caseARule(ARule node) {
    this.terms.clear();
    this.lhsterms.clear();
    this.sorts.clear();
    this.vars.clear();
    this.varnamegen = new FreshNameGenerator(this.usedNames, FreshNameGenerator.VARIABLES);
    this.sorts.push(this.curfun.getSort());
    this.sorts.push(this.curfun.getSort());
    this.lhs = true;
    this.visitedrootsymbol = false;
    node.getLeft().apply(this);
    AlgebraTerm left = this.lhsterms.pop();
    this.curleft = left;
    this.lhs = false;
    node.getRight().apply(this);
    this.defpatterns.add(left);
//    this.terms.pop().addRulesToProg(this.prog, this.curfun, left);
    LinkedHashSet<Rule> rules = this.terms.pop().getRules(left);
    this.curfunRules.addAll(rules);
    }

    @Override
    public void caseAOprule(AOprule node) {
    this.terms.clear();
    this.lhsterms.clear();
    this.sorts.clear();
    this.vars.clear();
    this.sorts.push(this.curfun.getSort());
    this.sorts.push(this.curfun.getSort());
    this.lhs = true;
    this.visitedrootsymbol = false;
    node.getLeft().apply(this);
    AlgebraTerm left = this.lhsterms.pop();
    this.curleft = left;
    this.lhs = false;
    node.getRight().apply(this);
    this.defpatterns.add(left);
//    this.terms.pop().addRulesToProg(this.prog, this.curfun, left);
    LinkedHashSet<Rule> rules = this.terms.pop().getRules(left);
    this.curfunRules.addAll(rules);
    }

    @Override
    public void caseAIfLongSterm(AIfLongSterm node) {
    if (!this.chop(node.getThen()).equals("then")) {
        this.addParseError(node.getThen(), "''then'' expected");
        return;
    }
    if (!this.chop(node.getElse()).equals("else")) {
        this.addParseError(node.getElse(), "''else'' expected");
        return;
    }
    this.caseAIf(node.getCondTerm(), node.getThenTerm(), node.getElseTerm(), node.getIf());
    }

    @Override
    public void caseAIfShortSterm(AIfShortSterm node) {
    this.caseAIf(node.getCondTerm(), node.getThenTerm(), node.getElseTerm(), node.getIf());
    }

    private void caseAIf(PTerm co, PTerm th, PTerm el, Token tif) {
    Sort s = (Sort)this.sorts.pop();
    if (this.lhs) {
        this.addParseError(tif, "cannot use built-in ''if'' on lhs");
        this.pushdummyterm(s);
        return;
    }
    this.sorts.push(s);
    this.sorts.push(s);
    this.sorts.push(this.prog.getSort("bool"));
    co.apply(this);
    th.apply(this);
    el.apply(this);
    CondTerm tel = (CondTerm)this.terms.pop();
    CondTerm tth = (CondTerm)this.terms.pop();
    CondTerm tco = (CondTerm)this.terms.pop();
    CondTerm term = CondTerm.createIf(tco, tth, tel, this.prog);
    this.terms.push(term);
    }

    @Override
    public void caseALetSterm(ALetSterm node) {
    if (this.lhs) {
        this.addParseError(node.getLet(), "cannot use built-in ''let'' on lhs");
        return;
    }
    this.letListStack.push(this.letList);
    this.letTermsStack.push(this.letTerms);
    this.letList = new Vector<CondTerm>();
    this.letTerms = new Vector<AlgebraTerm>();
    Hashtable oldletvars = new Hashtable(this.letvars);
    HashMap<VariableSymbol, CondTerm> oldLetReplacements = new HashMap<VariableSymbol, CondTerm>(this.letReplacements);
    Vector<String> oldForbiddenLetVars = new Vector<String>(this.forbiddenLetVars);
    node.getLetlist().apply(this);
    this.forbiddenLetVars.removeAll(this.letvars.keySet());
    node.getTerm().apply(this);
//    CondTerm term = (CondTerm)this.terms.pop();
//    Iterator l_it = letList.iterator();
//    Iterator lt_it = letTerms.iterator();
//    while (l_it.hasNext()) {
//        CondTerm let = (CondTerm)l_it.next();
//        Term lett = (Term)lt_it.next();
//        term = CondTerm.createLet(let, lett, term);
//    }
//    this.terms.push(term);
    this.forbiddenLetVars = oldForbiddenLetVars;
    this.letReplacements = oldLetReplacements;
    this.letList = (Vector<CondTerm>)this.letListStack.pop();
    this.letTerms = (Vector<AlgebraTerm>)this.letTermsStack.pop();
    this.letvars = oldletvars;
    }

    @Override
    public void caseALetlist(ALetlist node) {
    // the following line does not work for programs like let u=let z=... in z in u
//    Sort s = this.getSort(node.getTerm());
    Token id = node.getId();
    String name = this.chop(id);

//    this.sorts.push(s);
    this.sorts.push(Pass.FP_UNKNOWN_SORT);
    this.forbiddenLetVars.insertElementAt(name, 0);
    node.getTerm().apply(this);
    this.forbiddenLetVars.remove(name);

    // getting the sort by looking at the resulting CondTerm
    // assuming that all CondTermTuples terms in the CondTerm's set have the same sort
    CondTerm ct = this.terms.peek();
    Sort s = ((CondTermTuple)ct.iterator().next()).term.getSort();

    if (this.vars.containsKey(name) || this.prog.getFunctionSymbol(name) != null) {
        this.addParseError(id, "''"+name+"'' is allready used");
        this.pushdummyterm(s);
        return;
    }
    VariableSymbol vsym = VariableSymbol.create(this.varnamegen.getFreshName(name, false), s);
    AlgebraVariable v = AlgebraVariable.create(vsym);
    this.letvars.put(name, vsym);

    this.letReplacements.put(vsym, this.terms.peek());
    this.letTerms.insertElementAt(v,0);
    this.letList.insertElementAt(this.terms.pop(),0);

    PNextletlist nextlist = node.getNextletlist();
    if (nextlist != null) {
        nextlist.apply(this);
    }
    }

    public void caseADequalTerm(AOperatorTerm node) {
    Sort s = (Sort)this.sorts.pop();
     Sort bool = this.prog.getSort("bool");
    if (this.lhs) {
        this.addParseError(node.getInfixid(), "use of ''=='' not allowed in lhs");
        this.pushdummyterm(s);
        return;
    }
    if (!this.checksorts(bool, s, node.getInfixid())) {
        this.pushdummyterm(s);
        return;
    }
    s = this.getSort(node.getLeft());
    if (s == null) {
        return;
    }
    this.sorts.push(s);
    this.sorts.push(s);
    node.getLeft().apply(this);
    node.getRight().apply(this);
        SyntacticFunctionSymbol f = this.prog.getPredefFunctionSymbol("equal_"+s.getName());
    if (f == null) {
        if (!s.equals(Pass.FP_UNKNOWN_SORT)) {// suppressing confusing output
            this.addParseError(node.getInfixid(), "internal error: ''equal_"+s.getName()+"'' not found!");
        }
        else {
            this.addParseError(node.getInfixid(), "sort of lhs could not be inferred");
        }
    } else {
            try {
                this.prog.activatePredefFunctionSymbol(f.getName());
            } catch (ProgramException e) {
                this.addParseError(node.getInfixid(), e.getMessage());
            }
        this.addarguments_rhs(f, 2);
    }
    }

    /** Gets the sort of the term be descending leftmost until a token
     *  is found that determines the sort.
     */
    private Sort getSort(Node p) {
    Token token = null;
    Sort s = null;
     Sort bool = this.prog.getSort("bool");
    while (s == null) {
        if (p instanceof AStermTerm) {
        p = ((AStermTerm)p).getSterm();
        }
        else if (p instanceof AOperatorTerm) {
        token = ((AOperatorTerm)p).getInfixid();
        if (this.chop(token).equals("==")) {
            s = this.prog.getSort("bool");
        }
        else {
            Symbol sym = this.prog.getSymbol(this.chop(token));
            if (sym == null) {
            this.addParseError(token, "Unknown function-symbol ''"+this.chop(token)+"''");
            }
            s = sym.getSort();
        }
        }
        else if (p instanceof AIfLongSterm) {
        p = ((AIfLongSterm)p).getThenTerm();
        }
        else if (p instanceof AIfShortSterm) {
        p = ((AIfShortSterm)p).getThenTerm();
        }
        else if (p instanceof ATtermSterm) {
        p = ((ATtermSterm)p).getTterm();
        }
        else if (p instanceof AConstVarTterm) {
        token = ((AConstVarTterm)p).getId();
        Symbol sym = this.prog.getSymbol(this.chop(token));
        if (sym == null) {
            sym = (Symbol)this.vars.get(this.chop(token));
            if (sym == null) {
                sym = (Symbol)this.letvars.get(this.chop(token));
            }
            if (sym == null) {
            this.addParseError(token, "Unknown variable ''"+this.chop(token)+"''");
            this.pushdummyterm(bool);
            return null;
            }
        }
        s = sym.getSort();
        }
        else if (p instanceof AFunctAppTterm) {
        token = ((AFunctAppTterm)p).getId();
        Symbol sym = this.prog.getSymbol(this.chop(token));
        if (sym == null) {
            sym = this.prog.getPredefFunctionSymbol(this.chop(token));
            if (sym == null) {
            this.addParseError(token, "Unknown function ''"+this.chop(token)+"''");
            this.pushdummyterm(bool);
            return null;
            }
        }
        s = sym.getSort();
        }
        else if (p instanceof AParTterm) {
        p = ((AParTterm)p).getTerm();
        }
        else if (p instanceof ALetSterm) {
        p = ((ALetSterm)p).getTerm();
        }
    }
    return s;
    }

    @Override
    public void caseACasting(ACasting node) {
        Sort castSort = this.prog.getSort(this.chop(node.getSort()));
        if (castSort == null) {
            this.addParseError(node.getSort(), "Sort ''"+this.chop(node.getSort())+"'' is unknown");
        }
        else {
            this.sorts.pop();
            this.sorts.push(castSort);
        }
    }

    @Override
    public void caseAConstVarTterm(AConstVarTterm node) {
       if (node.getCasting() != null) {
           node.getCasting().apply(this);
       }
    this.constvar(node.getId());
    }

    @Override
    public void caseAUnaryTterm(AUnaryTterm node) {

        // currently only for integers unary operators are supported
        Sort intSort = IntegerTools.getIntSort(this.prog);
        Sort s = this.sorts.peek();
        if (!this.checksorts(s,intSort,node.getUnary())) {
            this.pushdummyterm(s);
            return;
        }

        String unaryOpName = this.chop(node.getUnary());
        List<String> unaryPredefs = Arrays.asList("+", "-");
        if (!unaryPredefs.contains(unaryOpName)) {
            this.addParseError(node.getUnary(), "unary operator ''"+unaryOpName+"'' is unknown.");
            this.pushdummyterm(s);
            return;
        }

        node.getTterm().apply(this);

        if (this.lhs) {
            AlgebraTerm negTerm = this.lhsterms.pop();
            negTerm = (new IntegerNegPredef(unaryOpName, this.typeContext, this.prog, negTerm)).toTerm();
            this.lhsterms.push(negTerm);
        }
        else {
            CondTerm negCondTerm = this.terms.pop();

            // if there is only one term in the condTerm, we might be able to negate it making it a function application
            if (negCondTerm.size() == 1) {
                Iterator<CondTermTuple> nctt_it = negCondTerm.iterator();
                AlgebraTerm negTerm = nctt_it.next().term;
                negTerm = (new IntegerNegPredef(this.chop(node.getUnary()), this.typeContext, this.prog, negTerm)).toTerm();
                negCondTerm = CondTerm.create(negTerm);
            }
            else {
                SyntacticFunctionSymbol negSym = IntegerNegPredef.getNegSymbol(this.typeContext, this.prog);
                CondTerm negCondTermArgs[] = new CondTerm[1];
                negCondTermArgs[0] = negCondTerm;
                negCondTerm = CondTerm.createApp(negSym, negCondTermArgs);
            }

            this.terms.push(negCondTerm);
        }
    }

    @Override
    public void caseAConstVarLterm(AConstVarLterm node) {
        this.constvar(node.getId());
    }


    private void constvar(Token id) {
    String name = this.chop(id);
    if (
            // is a variable name that already occured either on a lhs of let
            this.forbiddenLetVars.contains(name)
            &&
            // is not yet declared (i.e. reused directly in its own definition),
            // or it is not in the current scope (i.e. reused in its own definition and not locally overwritten)
            (!this.letvars.containsKey(name) || !this.letTerms.contains(this.letvars.get(name)))
       )
    {
        this.addParseError(id, "cannot reuse let-variable ''"+name+"'' (no recursion allowed inside ''let'')");
        this.pushdummyterm(this.sorts.pop());
        return;
    }
     Sort s = (Sort)this.sorts.pop();

     // handling of integers
     String intStr = name;
     if (this.containsInts && IntegerPredefItem.isIntegerString(intStr)) {
         AlgebraTerm intTerm = (new IntegerPredefItem(intStr, this.typeContext, this.prog).toTerm());

         if (!this.checksorts(s, intTerm.getSort(), id)) {
            this.addParseError(id, "sort ''"+s+"'' expected, but sort ''"+intTerm.getSort()+"'' found.");
            this.pushdummyterm(s);
            return;
        }
        if (this.lhs) {
            this.lhsterms.push(intTerm);
        }
        else {
            CondTerm ct = CondTerm.create(intTerm);
            this.terms.push(ct);
        }
        return;
     }


    Symbol sym = this.prog.getSymbol(name);
    if (sym == null) {  // not a function or constructor
        if (this.prog.getSort(name) != null) {
        this.addParseError(id, "cannot use structure symbol ''"+name+"'' in term");
        }
        sym = (Symbol)this.vars.get(name);
        boolean isLetVar = false;
        if (sym == null) {
            sym = (Symbol)this.letvars.get(name);
            isLetVar = (sym != null); // sym == null occurs for new variables
        }
        if (sym == null) { // new variable
                if (this.lhs) { // new variable on lhs
                    sym = VariableSymbol.create(name, s);
                    this.vars.put(name, (VariableSymbol)sym);
                } else { // no new variables may occur on rhs
                    sym = VariableSymbol.create(name, s);
                    this.addParseError(id, "variable ''"+name+"'' not declared in lhs");
        }
        } else {
        // On lhs variables may not appear twice.
        if (this.lhs) {
            this.addParseError(id, "variable ''"+name+"'' appeared twice in lhs");
            this.pushdummyterm(s);
            return;
        }
        if (sym instanceof SyntacticFunctionSymbol) {
            this.addParseError(id, "expected variable or constructor, but function ''"+
                this.chop(id)+"'' found (perhaps ''()'' missing)");
            this.pushdummyterm(s);
            return;
        }
        if (!this.checksorts(s, sym.getSort(), id)) {
            this.pushdummyterm(s);
            return;
        }
        }
        if (this.lhs) {
            this.lhsterms.add(AlgebraVariable.create((VariableSymbol)sym));
        } else {
            if (isLetVar) {
                CondTerm letRHS = this.letReplacements.get(sym);
                CondTerm replace = letRHS.deepcopy();
                this.terms.add(replace);
            }
            else {
                this.terms.add(CondTerm.create(AlgebraVariable.create((VariableSymbol)sym)));
            }
        }
    } else {
        if (((SyntacticFunctionSymbol)sym).getArity() != 0) {
        this.addParseError(id, "missing parameter list for function or constructor ''"+name+"''");
        }
        if (!this.checksorts(s, sym.getSort(), id)) {
        this.pushdummyterm(s);
        return;
        }
        if (this.lhs) {
            this.lhsterms.add(AlgebraFunctionApplication.create((SyntacticFunctionSymbol)sym));
        } else {
            this.terms.add(CondTerm.create(AlgebraFunctionApplication.create((SyntacticFunctionSymbol)sym)));
        }
    }
    }



    @Override
    public void caseAFunctAppTterm(AFunctAppTterm node) {
    this.functapp(node.getId(), node.getTermlist());
    }

    @Override
    public void caseAFunctAppLterm(AFunctAppLterm node) {
    this.functapp(node.getId(), node.getTermlist());
    }

    @Override
    public void caseAIsaTterm(AIsaTterm node) {
    String name = this.chop(node.getIsa());
    Sort bool = this.prog.getSort("bool");
    if (!this.checksorts((Sort)this.sorts.pop(), bool, node.getIsa())) {
        return;
    }
    DefFunctionSymbol isa = this.prog.getDefFunctionSymbol(name);
    if (isa == null) {
        isa = this.prog.getPredefFunctionSymbol(name);
        try {
        this.prog.activatePredefFunctionSymbol(name);
        }
        catch (ProgramException e) {
        isa = null;
        }
    }
    if (isa == null) {
        this.addParseError(node.getIsa(), "Cannot associate '"+name+"' with a sort.");
        this.pushdummyterm(bool);
        return;
    }
    this.sorts.push(isa.getArgSort(0));
    node.getTerm().apply(this);
    CondTerm args[] = new CondTerm[1];
    args[0] = (CondTerm)this.terms.pop();
    this.terms.push(CondTerm.createApp(isa, args));
    }

    private void functapp(Token id, PTermlist termlist) {
    String name = this.chop(id);
    Sort s = (Sort)this.sorts.pop();
    if (this.chop(id).equals("and")) {
        name = Pass.AND_NAME;
    }
    else if (this.chop(id).equals("or")) {
        name = Pass.OR_NAME;
    }

    SyntacticFunctionSymbol f = null;
    int numArgs = ((ATermlist)termlist).getTermcomma().size()+1;
    if ( ((ATermlist)termlist).getTerm() == null ) {
        --numArgs;
    }

    f = this.prog.getFunctionSymbol(name);


    // if this is the lhs-rootsymbol it has to be the current function
    if (!this.visitedrootsymbol && !this.chop(this.curfuntoken).equals(this.chop(id))) {
        this.addParseError(id, "Found definition for ''"+this.chop(id)+
            "'' but expected definiton for ''"+this.chop(this.curfuntoken)+"''.");
    }
    // the constructor/function has to be declared
    if (f == null) {
        f = this.prog.getPredefFunctionSymbol(this.chop(id));
        if (f == null) {
               this.addParseError(id, "undeclared function or constructor ''"+ this.chop(id)+"''");
            this.pushdummyterm(s);
            return;
        }
        try {
            this.prog.activatePredefFunctionSymbol(this.chop(id));
        } catch (ProgramException e) {
            this.addParseError(id, e.getMessage());
        }
    }

    if (PredefDataStructureSymbols.isPredefinedSymbol(f)) {
        this.addParseError(id, "you are not allowed to use predefined data structure symbol ''"+f.getName()+"''.");
        this.pushdummyterm(s);
        return;
    }

    // all arguments of the lhs-rootsymbol have to be constructorterms
    if (this.lhs && this.visitedrootsymbol && f instanceof DefFunctionSymbol) {
        this.addParseError(id,
            "arguments of defining terms have to be constructorterms, but ''"+this.chop(id)+
            "'' is a function.");
    }
    this.visitedrootsymbol = true;
    if (!this.checksorts(s, f.getSort(), id)) {
        this.pushdummyterm(s);
        return;
    }

    for (int i=f.getArity()-1; i>=0; i--) {this.sorts.push(f.getArgSort(i));}
    if (f.getArity() != numArgs) {
        this.addParseError(id,
            "expected "+ Integer.valueOf(f.getArity()).toString()+
            " parameters, not "+ Integer.valueOf(numArgs).toString());
        this.pushdummyterm(s);
        return;
    }

    // after having pushed all expected sorts, process the arguments
    termlist.apply(this);

    if (this.lhs) {
        this.addarguments_lhs(f, numArgs);
    } else {
        this.addarguments_rhs(f, numArgs);
    }
    }

    private void addarguments_lhs(SyntacticFunctionSymbol f, int numArgs) {
       List<AlgebraTerm> largs = null;
    largs = new Vector<AlgebraTerm>();
    for(int i=0; i<numArgs; ++i) {
        largs.add(0, this.lhsterms.pop());
    }
    if (f instanceof DefFunctionSymbol) {
        this.lhsterms.add(DefFunctionApp.create((DefFunctionSymbol)f, largs));
    } else {
        this.lhsterms.add(ConstructorApp.create((ConstructorSymbol)f, largs));
    }
    }

    private void addarguments_rhs(SyntacticFunctionSymbol f, int n) {
        CondTerm t[] = new CondTerm[n];
        try {
            for (int i=n-1; i>=0; i--) {
            t[i]=(CondTerm)this.terms.pop();
            }
        } catch (EmptyStackException e) {
            return;
        }
        this.terms.add(CondTerm.createApp(f, t));
    }

    @Override
    public void caseAOperatorTerm(AOperatorTerm node) {
    Token id = node.getInfixid();
    if (this.chop(id).equals("==")) {
        this.caseADequalTerm(node);
        return;
    }
    Sort s = (Sort)this.sorts.pop();
    String name = this.chop(id);
    if (name.equals("\u2228")) {
        name = Pass.OR_NAME;
    }
    else if (name.equals("\u2227")) {
        name = Pass.AND_NAME;
    }

    SyntacticFunctionSymbol f;
    SyntacticFunctionSymbol intPredef = null;

    // try to get the function
    f = this.prog.getFunctionSymbol(name);
    if ( (f == null) && (this.containsInts) ) {
        // look for predefined Integer operator
        f = this.getIntegerPredefOperator(this.chop(id),id);
    }



    // if this is the lhs-rootsymbol it has to be the current function
    if (!this.visitedrootsymbol && !this.chop(this.curfuntoken).equals(this.chop(id))) {
        this.addParseError(id,
            "Found definition for ''"+this.chop(id)+
            "'' but expected definiton for ''"+this.chop(this.curfuntoken)+"''.");
    }


    // the function has to be declared
    if (f == null) {
        if (name.equals("||")) {
            name = Pass.OR_NAME;
        } else if (name.equals("&&")) {
            name = Pass.AND_NAME;
        }
        f = this.prog.getPredefFunctionSymbol(name);
        if (f == null) {
        this.addParseError(id,
                "undeclared function or constructor ''"+this.chop(id)+"''");
        this.pushdummyterm(s);
        return;
        }
            try {
        this.prog.activatePredefFunctionSymbol(name);
            } catch (ProgramException e) {
                this.addParseError(id, e.getMessage());
            }
    }
    // all arguments of the lhs-rootsymbol have to be constructorterms
    if (this.lhs && this.visitedrootsymbol && f instanceof DefFunctionSymbol) {
        this.addParseError(id,
            "arguments of defining terms have to be constructorterms, but ''"+this.chop(id)+
            "'' is a function.");
    }
    this.visitedrootsymbol = true;
    if (!this.checksorts(s, f.getSort(), id)) {
        this.pushdummyterm(s);
        return;
    }
    if (this.lhs) {
        AlgebraTerm t[] = new AlgebraTerm[2];
        this.sorts.push(f.getArgSort(0));
        node.getLeft().apply(this);
        t[0] = this.lhsterms.pop();
        this.sorts.push(f.getArgSort(1));
        node.getRight().apply(this);
        t[1] = this.lhsterms.pop();
        if (f instanceof DefFunctionSymbol) {
        this.lhsterms.add(DefFunctionApp.create((DefFunctionSymbol)f, t));
        }
        else {
        this.lhsterms.add(ConstructorApp.create((ConstructorSymbol)f, t));
        }
    }
    else {
        CondTerm t[] = new CondTerm[2];
        this.sorts.push(f.getArgSort(0));
        node.getLeft().apply(this);
        t[0] = (CondTerm)this.terms.pop();
        this.sorts.push(f.getArgSort(1));
        node.getRight().apply(this);
        t[1] = (CondTerm)this.terms.pop();
        this.terms.add(CondTerm.createApp(f, t));
    }
    }







    // helper for createAOperatorTerm that retrieves an Integer function with the specified name
    private DefFunctionSymbol getIntegerPredefOperator(String name, Token id) {

        DefFunctionSymbol intPredefFunc = null;

        // looking for the predefined Integer function symbols
        List<String> intPredefs = Arrays.asList("+", "-", "*", "/", "<", "<=", ">", ">=", "%");

        // will be -1 if name is not contained
        int predefIndex  = intPredefs.indexOf(name);

        if (predefIndex >= 0) {
            switch(predefIndex) {
                case 0:  // "+"
                    intPredefFunc = IntegerPlusPredef.getPlusSymbol(this.typeContext, this.prog);
                    break;

                case 1:  // "-"
                    intPredefFunc = IntegerMinusPredef.getMinusSymbol(this.typeContext, this.prog);
                    break;

                case 2:  // "*"
                    intPredefFunc = IntegerMultPredef.getMultSymbol(this.typeContext, this.prog);
                    break;

                case 3:  // "/"
                    intPredefFunc = IntegerQuotPredef.getQuotSymbol(this.typeContext, this.prog);
                    break;

                case 4:  // "<"
                    intPredefFunc = IntegerLessEqPredef.getLessSymbol(this.typeContext, this.prog);
                    break;
                case 5:  // "<="
                    intPredefFunc = IntegerLessEqPredef.getLessEqSymbol(this.typeContext, this.prog);
                    break;

                case 6:  // ">"
                    intPredefFunc = IntegerGreaterEqPredef.getGreaterSymbol(this.typeContext, this.prog);
                    break;
                case 7:  // ">="
                    intPredefFunc = IntegerGreaterEqPredef.getGreaterEqSymbol(this.typeContext, this.prog);
                    break;

                case 8:  // "%"
                    intPredefFunc = IntegerModPredef.getModSymbol(this.typeContext, this.prog);
                    break;

                default:  // ERROR: unknown operator
                    this.addParseError(id, "Internal Error: Integer predefined operator expected, but ,,"+name+"'' is not handled.");
            }
        }

        return intPredefFunc;
    }


}
