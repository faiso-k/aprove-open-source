package aprove.verification.oldframework.Verifier;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** This class provides the rewrite-calculus-verifier. This is a simple
 *  verifier to quickly verify theorems which do not need induction.
 *  The methodes make a few assumptions which have to be true:
 *  - Every function whose name is of the form equal_/type/ has to
 *    be an equality-function for the correspondent type.
 *  - and/or/not has to be the boolean function for and/or/not.
 *  - bool has to be the boolean type whose constructors have to
 *    be true and false.
 *  @author Christian Haselbach
 *  @version $Id$
 */

public class RewriteCalculus {

    protected Program prog;
    private FreshNameGenerator symbnames;
    protected Map defsrules;
    private Sort bool;
    private DefFunctionSymbol fAnd;
    private DefFunctionSymbol fOr;
    private DefFunctionSymbol fNot;
    private ConstructorSymbol cTrue;
    private ConstructorSymbol cFalse;

    private TypeContext typeContext;
    private TypeDefinition boolTypeDef;

    protected Hashtable definedChecks;
    public static final int maxNrOfCaseAnalyses = 2;
    public static final int CA_NORMAL = 0;
    public static final int CA_RECURSION_SHIFT = 1;
    public int caseAnalysesType = RewriteCalculus.CA_NORMAL;

    protected static final int RWLABELLIMIT = 2;
    protected static final int RWITERLIMIT = 20;
    protected static final int RWDEPTHLIMIT = 10;


    /* Constructors */

    protected RewriteCalculus(Program prog, Map defsrules, TypeContext typeContext) {
    this.prog = prog;
    this.defsrules = defsrules;
    this.bool = prog.getSort("bool");

    this.typeContext = typeContext.deepcopy();
    this.boolTypeDef = this.typeContext.getTypeDef("bool");

    this.fAnd = prog.getDefFunctionSymbol("and");
    if (this.fAnd == null) {
        this.fAnd = prog.getPredefFunctionSymbol("and");
        if (this.fAnd == null) {
        this.fAnd = prog.getDefFunctionSymbol("&&");
        if (this.fAnd == null) {
            this.fAnd = prog.getPredefFunctionSymbol("&&");
        }
        }
    }
    if (this.defsrules.get(this.fAnd) == null) {
        Set<Rule> rules = prog.getRules(this.fAnd);
        this.defsrules.put(this.fAnd, rules);
    }
    this.fOr = prog.getDefFunctionSymbol("or");
    if (this.fOr == null) {
        this.fOr = prog.getPredefFunctionSymbol("or");
        if (this.fOr == null) {
        this.fOr = prog.getDefFunctionSymbol("||");
        if (this.fOr == null) {
            this.fOr = prog.getPredefFunctionSymbol("||");
        }
        }
    }
    if (this.defsrules.get(this.fOr) == null) {
        Set<Rule> rules = prog.getRules(this.fOr);
        this.defsrules.put(this.fOr, rules);
    }
    this.fNot = prog.getDefFunctionSymbol("not");
    if (this.fNot == null) {
        this.fNot = prog.getPredefFunctionSymbol("not");
    }
    if (this.defsrules.get(this.fNot) == null) {
        Set<Rule> rules = prog.getRules(this.fNot);
        this.defsrules.put(this.fNot, rules);
    }
    this.cTrue = prog.getConstructorSymbol("true");
    this.cFalse = prog.getConstructorSymbol("false");
    Set<String> used = new HashSet<String>(prog.getSignature());
    Iterator it = defsrules.keySet().iterator();
    while (it.hasNext()) {
        used.add(((DefFunctionSymbol)it.next()).getName());
    }
    this.symbnames = new FreshNameGenerator(used, FreshNameGenerator.VARIABLES);
    this.createDefinedChecks();
    // Make advanced and-function.
    Set<Rule> rules = new HashSet<Rule>();
    String name = this.symbnames.getFreshName("x", true);
    AlgebraVariable v = AlgebraVariable.create(VariableSymbol.create(name, this.bool));
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    args.add(v);
    args.add(AlgebraFunctionApplication.create(this.cTrue));
    AlgebraTerm left = AlgebraFunctionApplication.create(this.fAnd, args);
    rules.add(Rule.create(left, v.shallowcopy()));
    args = new Vector<AlgebraTerm>();
    args.add(AlgebraFunctionApplication.create(this.cTrue));
    args.add(v);
    left = AlgebraFunctionApplication.create(this.fAnd, args);
    rules.add(Rule.create(left, v.shallowcopy()));
    args = new Vector<AlgebraTerm>();
    args.add(v);
    args.add(AlgebraFunctionApplication.create(this.cFalse));
    left = AlgebraFunctionApplication.create(this.fAnd, args);
    rules.add(Rule.create(left, AlgebraFunctionApplication.create(this.cFalse)));
    args = new Vector<AlgebraTerm>();
    args.add(AlgebraFunctionApplication.create(this.cFalse));
    args.add(v);
    left = AlgebraFunctionApplication.create(this.fAnd, args);
    rules.add(Rule.create(left, AlgebraFunctionApplication.create(this.cFalse)));
    this.defsrules.put(this.fAnd, rules);
    // Make advanced or-function.
    rules = new HashSet<Rule>();
    args = new Vector<AlgebraTerm>();
    args.add(v);
    args.add(AlgebraFunctionApplication.create(this.cFalse));
    left = AlgebraFunctionApplication.create(this.fOr, args);
    rules.add(Rule.create(left, v.shallowcopy()));
    args = new Vector<AlgebraTerm>();
    args.add(AlgebraFunctionApplication.create(this.cFalse));
    args.add(v);
    left = AlgebraFunctionApplication.create(this.fOr, args);
    rules.add(Rule.create(left, v.shallowcopy()));
    args = new Vector<AlgebraTerm>();
    args.add(v);
    args.add(AlgebraFunctionApplication.create(this.cTrue));
    left = AlgebraFunctionApplication.create(this.fOr, args);
    rules.add(Rule.create(left, AlgebraFunctionApplication.create(this.cTrue)));
    args = new Vector<AlgebraTerm>();
    args.add(AlgebraFunctionApplication.create(this.cTrue));
    args.add(v);
    left = AlgebraFunctionApplication.create(this.fOr, args);
    rules.add(Rule.create(left, AlgebraFunctionApplication.create(this.cTrue)));
    this.defsrules.put(this.fOr, rules);
    // Makde advanced equal-functions.

    for(TypeDefinition td : this.typeContext.getTypeDefs()) {

        // TODO removal of sorts
        // It is required that the sort and the type have the same names
        Sort s = prog.getSort(td.getDefTerm().getSymbol().getName());

        name = "equal_"+td.getDefTerm().getSymbol().getName();

        DefFunctionSymbol eq = this.prog.getDefFunctionSymbol(name);
        if (eq == null) {
        eq = prog.getPredefFunctionSymbol(name);
        }
        name = this.symbnames.getFreshName("x", true);
        v = AlgebraVariable.create(VariableSymbol.create(name, s));
        args = new Vector<AlgebraTerm>();
        args.add(v);
        args.add(v.shallowcopy());
        left = AlgebraFunctionApplication.create(eq, args);
        AlgebraTerm right = AlgebraFunctionApplication.create(this.cTrue);
        rules = new HashSet<Rule>(this.prog.getRules(eq));
        rules.add(Rule.create(left, right));
        this.defsrules.put(eq, rules);
    }
    }

    /** Creates for every sort a defined-function which terminates
     *  iff a given term terminates. If def terminates it returns
     *  true.
     */
    protected void createDefinedChecks() {
        this.definedChecks = new Hashtable();
        // At first create the function-symbols.
        Sort bool = this.cTrue.getSort();

        AlgebraTerm boolType = this.typeContext.getSingleTypeOf(this.cTrue).getTypeMatrix();

        Vector<DefFunctionSymbol> fsyms = new Vector<DefFunctionSymbol>();

        for(TypeDefinition td : this.typeContext.getTypeDefs()) {

            String name = this.symbnames.getFreshName("def_"+td.getDefTerm(), true);

            // TODO removal of sorts
            Sort s = Sort.create(td.getDefTerm().toString());
            Vector<Sort> sorts = new Vector<Sort>();
            sorts.add(s);

            DefFunctionSymbol fsym = DefFunctionSymbol.create(name, sorts, bool);

            Vector<AlgebraTerm> fsymArgsTypes = new Vector<AlgebraTerm>();
            AlgebraTerm arg0WitnessType = TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(td.getWitnessTerm().getSymbol()).getTypeMatrix());
            fsymArgsTypes.add(arg0WitnessType);

            this.typeContext.setSingleTypeOf( fsym, new Type(TypeTools.function(fsymArgsTypes, boolType)) );

            fsyms.add(fsym);
            this.definedChecks.put(td.getDefTerm().getSymbol().getName(), fsym);
        }
        // Then create the rules.
        for(DefFunctionSymbol def : fsyms) {
            AlgebraTerm defArg0Type = TypeTools.getFunctionArgAt(this.typeContext.getSingleTypeOf(def).getTypeMatrix(),0);
            TypeDefinition defArg0TypeDef = this.typeContext.getTypeDef(defArg0Type.getSymbol().getName());

            Set<Rule> defrules = new HashSet<Rule>();

            Iterator c_it = defArg0TypeDef.getDeclaredSymbols().iterator();
            while (c_it.hasNext()) {
                ConstructorSymbol csym = (ConstructorSymbol)c_it.next();
                Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();

                for(int i=0; i<csym.getArity(); ++i) {
                    // TODO removal of sorts
                    Sort as = csym.getArgSort(i);

                    String name = this.symbnames.getFreshName("x_"+(i+1), true);
                    args.add(AlgebraVariable.create(VariableSymbol.create(name, as)));
                }

                AlgebraTerm larg = AlgebraFunctionApplication.create(csym, args);
                Vector<AlgebraTerm> largs = new Vector<AlgebraTerm>();
                largs.add(larg);
                AlgebraTerm left = AlgebraFunctionApplication.create(def, largs);
                AlgebraTerm right = null;
                if (csym.getArity() == 0) {
                    right = AlgebraFunctionApplication.create(this.cTrue);
                }
                else {
                    Iterator a_it = args.iterator();
                    right = (AlgebraTerm)a_it.next();

                    Iterator<AlgebraTerm> it_ArgTypes = TypeTools.getFunctionArgs(this.typeContext.getSingleTypeOf(csym).getTypeMatrix()).iterator();
                    String tdName = it_ArgTypes.next().getSymbol().getName();

                    DefFunctionSymbol sdef = (DefFunctionSymbol)this.definedChecks.get(tdName);

                    Vector<AlgebraTerm> fargs = new Vector<AlgebraTerm>();
                    fargs.add(right.shallowcopy());
                    right = AlgebraFunctionApplication.create(sdef, fargs);
                    while (a_it.hasNext()) {
                        AlgebraTerm t = (AlgebraTerm)a_it.next();

                        tdName = it_ArgTypes.next().getSymbol().getName();
                        sdef = (DefFunctionSymbol)this.definedChecks.get(tdName);

                        fargs = new Vector<AlgebraTerm>();
                        fargs.add(t.shallowcopy());
                        Vector<AlgebraTerm> andargs = new Vector<AlgebraTerm>();
                        andargs.add(right);
                        andargs.add(AlgebraFunctionApplication.create(sdef, fargs));
                        right = AlgebraFunctionApplication.create(this.fAnd, andargs);
                    }
                }
                defrules.add(Rule.create(left, right));
            }
            this.defsrules.put(def, defrules);
        }
    }

    public static RewriteCalculus create(Program prog, Map defsrules, TypeContext typeContext) {
    return new RewriteCalculus(prog, new Hashtable(defsrules), typeContext);
    }


    /* Accessors */
    /*
    public void setDefsrules(Hashtable defsrules) {
    this.defsrules = defsrules;
    }
    */


    /* Rewrite-Step */

    public AlgebraTerm limitRewriteCondition(AlgebraTerm term, int limit) {
    if (term.isVariable()) {
        return null;
    }
    SyntacticFunctionSymbol sym = (SyntacticFunctionSymbol)term.getSymbol();
    if (sym instanceof DefFunctionSymbol) {
        if (!((DefFunctionSymbol)sym).getTermination()) {
        Hashtable label = (Hashtable)term.getAttribute("label");
        Integer count = (Integer)label.get(sym.getName());
        if (count == null || count.intValue() < limit) {
            Iterator it = this.getRules((DefFunctionSymbol)sym).iterator();
            while (it.hasNext()) {
            Rule r = (Rule)it.next();
            AlgebraTerm rewritten = term.rewrite(RewriteCalculus.RWLABELLIMIT, RewriteCalculus.RWITERLIMIT, RewriteCalculus.RWDEPTHLIMIT, r, this.defsrules, 0);
            if (rewritten != null) {
                count = Integer.valueOf(count == null ? 1 : count.intValue()+1);
                label.put(sym.getName(), count);
                rewritten.labelTerm(label);
                return rewritten;
            }
            }
        }
        }
        else {
        Iterator it = (this.getRules((DefFunctionSymbol)sym)).iterator();
        while (it.hasNext()) {
            Rule r = (Rule)it.next();
            AlgebraTerm rewritten = term.rewrite(RewriteCalculus.RWLABELLIMIT, RewriteCalculus.RWITERLIMIT, RewriteCalculus.RWDEPTHLIMIT, r, this.defsrules, 0);
            if (rewritten != null) {
            return rewritten;
            }
        }
        }
    }
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    boolean rewritten = false;
    Iterator it = term.getArguments().iterator();
    while (it.hasNext()) {
        AlgebraTerm ta = (AlgebraTerm)it.next();
        AlgebraTerm tan = this.limitRewriteCondition(ta, limit);
        if (tan != null) {
        rewritten = true;
        args.add(tan);
        while(it.hasNext()) {
            args.add((AlgebraTerm) it.next());
        }
        }
        else {
        args.add(ta);
        }
    }
    if (rewritten) {
        AlgebraTerm t = AlgebraFunctionApplication.create(sym, args);
        t.setAttributes(term.getAttributes());
        return t;
    }
    else {
        return null;
    }
    }

    public AlgebraTerm limitRewriteTerm(AlgebraTerm condition, AlgebraTerm term, int limit) {
    if (term.isVariable()) {
        return null;
    }
    SyntacticFunctionSymbol sym = (SyntacticFunctionSymbol)term.getSymbol();
    if (sym instanceof DefFunctionSymbol) {
        if (!((DefFunctionSymbol)sym).getTermination()) {
        Hashtable label = (Hashtable)term.getAttribute("label");
        Integer count = (Integer)label.get(sym.getName());
        if (count == null || count.intValue() < limit) {
            Iterator it = this.getRules((DefFunctionSymbol)sym).iterator();
            while (it.hasNext()) {
            Rule r = (Rule)it.next();
            AlgebraTerm left = r.getLeft();
            AlgebraTerm right = r.getRight();
            AlgebraSubstitution sub = null;
            try {
                sub = left.matches(term);
            }
            catch (UnificationException e) {
                continue;
            }
            AlgebraTerm rewritten = term.rewrite(RewriteCalculus.RWLABELLIMIT, RewriteCalculus.RWITERLIMIT, RewriteCalculus.RWDEPTHLIMIT, r, sub, this.defsrules, 0);
            if (rewritten != null && this.definednessFollows(condition, sub)) {
                count = Integer.valueOf(count == null ? 1 : count.intValue()+1);
                label.put(sym.getName(), count);
                right.labelTerm(label);
                return right.apply(sub);
            }
            }
        }
        }
        else {
        Iterator it = this.getRules((DefFunctionSymbol)sym).iterator();
        while (it.hasNext()) {
            Rule r = (Rule)it.next();
            AlgebraTerm left = r.getLeft();
            AlgebraTerm right = r.getRight();
            AlgebraSubstitution sub = null;
            try {
            sub = left.matches(term);
            }
            catch (UnificationException e) {
            continue;
            }
            AlgebraTerm rewritten = term.rewrite(RewriteCalculus.RWLABELLIMIT, RewriteCalculus.RWITERLIMIT, RewriteCalculus.RWDEPTHLIMIT, r, sub, this.defsrules, 0);
            if (rewritten != null && this.definednessFollows(condition, sub)) {
            return right.apply(sub);
            }
        }
        }
    }
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    boolean rewritten = false;
    Iterator it = term.getArguments().iterator();
    while (it.hasNext()) {
        AlgebraTerm ta = (AlgebraTerm)it.next();
        AlgebraTerm tan = this.limitRewriteTerm(condition, ta, limit);
        if (tan != null) {
        rewritten = true;
        args.add(tan);
        while(it.hasNext()) {
            args.add((AlgebraTerm) it.next());
        }
        }
        else {
        args.add(ta);
        }
    }
    if (rewritten) {
        AlgebraTerm t = AlgebraFunctionApplication.create(sym, args);
        t.setAttributes(term.getAttributes());
        return t;
    }
    else {
        return null;
    }
    }

    public boolean limitRewriteCalculusPair(RewriteCalculusPair rwpair, int limit) {
    AlgebraTerm rewritten = null;
    List<AlgebraTerm> pterms = rwpair.getTerms();
    AlgebraTerm condition = rwpair.getCondition();
    Iterator it = pterms.iterator();
    while (rewritten==null && it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        rewritten = this.limitRewriteTerm(condition, t, limit);
    }
    if (rewritten!=null) {
        it.remove();
        pterms.add(rewritten);
        return true;
    }
    else {
        rewritten = this.limitRewriteCondition(condition, limit);
        if (rewritten!=null) {
        rwpair.setCondition(rewritten);
        return true;
        }
    }
    return false;
    }

    public boolean isRewriteable(RewriteCalculusPair rwpair) {
    List<AlgebraTerm> pterms = rwpair.getTerms();
    AlgebraTerm condition = rwpair.getCondition();
    Iterator it = pterms.iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        if (this.isRewriteable(condition, t)) {
        return true;
        }
    }
    if (this.isRewriteable(condition)) {
        return true;
    }
    return false;
    }

    public boolean isRewriteable(AlgebraTerm condition, AlgebraTerm term) {
    if (term.isVariable()) {
        return false;
    }
    SyntacticFunctionSymbol sym = (SyntacticFunctionSymbol)term.getSymbol();
    if (sym instanceof DefFunctionSymbol) {
        Iterator it = this.getRules((DefFunctionSymbol)sym).iterator();
        while (it.hasNext()) {
        Rule r = (Rule)it.next();
        AlgebraTerm left = r.getLeft();
        AlgebraTerm right = r.getRight();
        AlgebraSubstitution sub = null;
        try {
            sub = left.matches(term);
        }
        catch (UnificationException e) {
            continue;
        }
        if (this.definednessFollows(condition, sub)) {
            return true;
        }
        }
    }
    Iterator it = term.getArguments().iterator();
    while (it.hasNext()) {
        AlgebraTerm ta = (AlgebraTerm)it.next();
        if (this.isRewriteable(condition, ta)) {
        return true;
        }
    }
    return false;
    }

    public boolean isRewriteable(AlgebraTerm term) {
    if (term.isVariable()) {
        return false;
    }
    SyntacticFunctionSymbol sym = (SyntacticFunctionSymbol)term.getSymbol();
    if (sym instanceof DefFunctionSymbol) {
        Iterator it = this.getRules((DefFunctionSymbol)sym).iterator();
        while (it.hasNext()) {
        Rule r = (Rule)it.next();
        AlgebraTerm left = r.getLeft();
        AlgebraTerm right = r.getRight();
        AlgebraSubstitution sub = null;
        try {
            sub = left.matches(term);
        }
        catch (UnificationException e) {
            continue;
        }
        return true;
        }
    }
    Iterator it = term.getArguments().iterator();
    while (it.hasNext()) {
        AlgebraTerm ta = (AlgebraTerm)it.next();
        if (this.isRewriteable(ta)) {
        return true;
        }
    }
    return false;
    }


    /* Case-Analyses */

    public Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>> caseAnalyses(RewriteCalculusPair rwpair, List<AlgebraTerm> rwpairTermsTypes) {
    Vector rwpairslist = new Vector();
    Vector<Vector<Vector<AlgebraTerm>>> rwpairslistTermsTypes = new Vector<Vector<Vector<AlgebraTerm>>>();
    AlgebraTerm condition = rwpair.getCondition();
    LinkedHashSet<Pair<AlgebraTerm,AlgebraTerm>> anlTermsAndTypes = this.getCaseAnalysesTerms(rwpair.getTerm(0), rwpairTermsTypes.get(0));
    for(Pair<AlgebraTerm,AlgebraTerm> sAndType : anlTermsAndTypes) {
        AlgebraTerm s = sAndType.x;
        AlgebraTerm sType = sAndType.y;

        Pair<List<RewriteCalculusPair>,Vector<Vector<AlgebraTerm>>> rwpairsAndTermsTypes = this.caseAnalysis(rwpair, s, sType);
        List<RewriteCalculusPair> rwpairs = rwpairsAndTermsTypes.x;
        Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = rwpairsAndTermsTypes.y;
        if (rwpairs != null) {
        rwpairslist.add(rwpairs);
        rwpairslistTermsTypes.add(rwpairsTermsTypes);
        }
    }
    return new Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>>(rwpairslist, rwpairslistTermsTypes);
    }

    public Pair<List<RewriteCalculusPair>,Vector<Vector<AlgebraTerm>>> caseAnalysis(RewriteCalculusPair rwpair, AlgebraTerm s, AlgebraTerm sType) {
    int nrOfCaseAnalyses = rwpair.getNrOfCaseAnalyses();
    if (nrOfCaseAnalyses > RewriteCalculus.maxNrOfCaseAnalyses) {
        return new Pair<List<RewriteCalculusPair>,Vector<Vector<AlgebraTerm>>> (null, null);
    }
    nrOfCaseAnalyses++;
    AlgebraTerm condition = rwpair.getCondition();
    if (!this.definednessFollows(s, condition)) {
        return new Pair<List<RewriteCalculusPair>,Vector<Vector<AlgebraTerm>>> (null, null);
    }
    List<RewriteCalculusPair> rwpairs = new Vector<RewriteCalculusPair>();
    Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();
    List<AlgebraTerm> terms = rwpair.getTerms();
    TypeDefinition sTD = this.typeContext.getTypeDef(sType.getSymbol().getName());

    Iterator it = sTD.getDeclaredSymbols().iterator();

    while (it.hasNext()) {
        ConstructorSymbol csym = (ConstructorSymbol)it.next();
        // Constructing the replacement for s.
        List<DefFunctionSymbol> selectors = this.getSelectors(csym);
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        Iterator s_it = selectors.iterator();
        while (s_it.hasNext()) {
        DefFunctionSymbol sel = (DefFunctionSymbol)s_it.next();
        Vector<AlgebraTerm> selarg = new Vector<AlgebraTerm>();
        selarg.add(s.shallowcopy());
        args.add(AlgebraFunctionApplication.create(sel, selarg));
        }
        AlgebraTerm replacement = AlgebraFunctionApplication.create(csym, args);
        Hashtable replacements = new Hashtable();
        replacements.put(s, replacement);
        // Make new condition (newcondition==b):
        // b[s/c(d_1(s),...,d_n(s)] && s == c(d_1(s),...,d_n(s)
        AlgebraTerm newcondition = this.termReplace(condition, replacements);
        newcondition.labelUnlabeled(new Hashtable());
        boolean rewriteable = this.isRewriteable(newcondition);
        args = new Vector<AlgebraTerm>();
        args.add(s.shallowcopy());
        args.add(replacement.shallowcopy());

        DefFunctionSymbol eq = this.getEqualFunction(sType);

        AlgebraTerm b1 = AlgebraFunctionApplication.create(eq, args);
        args = new Vector<AlgebraTerm>();
        args.add(newcondition);
        args.add(b1);
        newcondition = AlgebraFunctionApplication.create(this.fAnd, args);
        // Make new terms.
        Vector<AlgebraTerm> newterms = new Vector<AlgebraTerm>();
        Vector<AlgebraTerm> newtermsTypes = new Vector<AlgebraTerm>();
        Iterator t_it = terms.iterator();
        while (t_it.hasNext()) {
            AlgebraTerm t = (AlgebraTerm)t_it.next();
            AlgebraTerm newt = t.deepcopy().termReplace(replacements);
            t.labelUnlabeled(new Hashtable());
            rewriteable = rewriteable || this.isRewriteable(newcondition.deepcopy(), newt);
            newterms.add(newt);
            if (!newt.isVariable()) {
                newtermsTypes.add(TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(newt.getSymbol()).getTypeMatrix()));
            } // else rewriteable will be false, thus null will be returned
        }
        RewriteCalculusPair newrwpair = new RewriteCalculusPair(newcondition, newterms);
        newrwpair.setNrOfCaseAnalyses(nrOfCaseAnalyses);
        if (!rewriteable) {
            return new Pair<List<RewriteCalculusPair>,Vector<Vector<AlgebraTerm>>> (null, null);
        }
        rwpairs.add(newrwpair);
        rwpairsTermsTypes.add(newtermsTypes);
    }
    return new Pair<List<RewriteCalculusPair>,Vector<Vector<AlgebraTerm>>>(rwpairs,rwpairsTermsTypes);
    }

    /** Returns a linked hash-set of terms in an order that is (hopefully)
     *  suitable for case-analyses.
     */
    protected LinkedHashSet<Pair<AlgebraTerm,AlgebraTerm>> getCaseAnalysesTerms(AlgebraTerm term, AlgebraTerm termType) {
    LinkedHashSet<Pair<AlgebraTerm,AlgebraTerm>> anlTermsAndTypes = new LinkedHashSet<Pair<AlgebraTerm,AlgebraTerm>>();
    switch (this.caseAnalysesType) {
        case CA_NORMAL:
        this.getCaseAnalysesTermsNormal(term, termType, null, anlTermsAndTypes);
        break;
        case CA_RECURSION_SHIFT:
        this.getCaseAnalysesTermsRecShift(term, termType, null, anlTermsAndTypes, new HashSet<AlgebraVariable>());
        break;
    }
    return anlTermsAndTypes;
    }

    protected void getCaseAnalysesTermsRecShift(AlgebraTerm term, AlgebraTerm termType, AlgebraTerm prevType, LinkedHashSet<Pair<AlgebraTerm,AlgebraTerm>> anlTermsAndTypes, Set<AlgebraVariable> vars) {
    if (term.isVariable()) {
        if (vars.add((AlgebraVariable) term)) {
        anlTermsAndTypes.add(new Pair<AlgebraTerm,AlgebraTerm>(term,termType));
        }
    }
    else {
        AlgebraTerm termTypeM = this.typeContext.getSingleTypeOf(term.getSymbol()).getTypeMatrix();
        AlgebraTerm curType = TypeTools.getResultTerm(termTypeM);

        Set<AlgebraVariable> tvars = term.getVars();
        if (anlTermsAndTypes.isEmpty() && tvars.size() == 1 && (prevType == null || !prevType.equals(curType))) {
        vars.addAll(tvars);
        anlTermsAndTypes.add(new Pair<AlgebraTerm,AlgebraTerm>(term,termType));
        }
        Iterator it = term.getArguments().iterator();
        Iterator<AlgebraTerm> it_termArgsTypes = TypeTools.getFunctionArgs(termTypeM).iterator();
        while (it.hasNext()) {
        this.getCaseAnalysesTermsRecShift((AlgebraTerm)it.next(), it_termArgsTypes.next(), curType, anlTermsAndTypes, vars);
        }
    }
    }

    protected void getCaseAnalysesTermsNormal(AlgebraTerm term, AlgebraTerm termType, AlgebraTerm prevType, LinkedHashSet<Pair<AlgebraTerm,AlgebraTerm>> anlTermsAndTypes) {
    if (term.isVariable()) {
        anlTermsAndTypes.add(new Pair<AlgebraTerm,AlgebraTerm>(term, termType));
    }
    else {
        AlgebraTerm termTypeM = this.typeContext.getSingleTypeOf(term.getSymbol()).getTypeMatrix();
        AlgebraTerm curType = TypeTools.getResultTerm(termTypeM);

        Iterator it = term.getArguments().iterator();
        Iterator<AlgebraTerm> it_termArgsTypes = TypeTools.getFunctionArgs(termTypeM).iterator();
        while (it.hasNext()) {
        this.getCaseAnalysesTermsNormal((AlgebraTerm)it.next(), it_termArgsTypes.next(), curType, anlTermsAndTypes);
        }
        if (term.getVars().size() == 1 && (prevType == null || !prevType.equals(curType))) {
        anlTermsAndTypes.add(new Pair<AlgebraTerm,AlgebraTerm>(term,termType));
        }
    }
    }


    /* Proof-Methods */

    public boolean proveSyntacticalEquivalence(AlgebraTerm t1, AlgebraTerm t1Type, AlgebraTerm t2, AlgebraTerm t2Type) {
    Vector<RewriteCalculusPair> rwpairs = new Vector<RewriteCalculusPair>();
    Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();

    if (t1Type != t2Type) {
        return false;
    }

    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    args.add(t1.shallowcopy());
    args.add(t2.shallowcopy());

    DefFunctionSymbol eq = this.getEqualFunction(t1Type);

    AlgebraTerm term = AlgebraFunctionApplication.create(eq, args);

    DefFunctionSymbol def = (DefFunctionSymbol)this.definedChecks.get(t1Type.getSymbol().getName());
    args = new Vector<AlgebraTerm>();
    args.add(t1);
    AlgebraTerm condition = AlgebraFunctionApplication.create(def, args);
    rwpairs.add(new RewriteCalculusPair(condition, term));
    args = new Vector<AlgebraTerm>();
    args.add(t2);
    condition = AlgebraFunctionApplication.create(def, args);
    rwpairs.add(new RewriteCalculusPair(condition, term));
    Vector<AlgebraTerm> rwpairTermsTypes = new Vector<AlgebraTerm>();
    rwpairTermsTypes.add(TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(eq).getTypeMatrix()));
    rwpairsTermsTypes.add(rwpairTermsTypes);
    return this.prove(rwpairs, rwpairsTermsTypes);
    }

    /** Returns true if equivalence of t1 and t2 could be prooved.
     */
    public boolean proveEquivalence(AlgebraTerm t1, AlgebraTerm t1Type, AlgebraTerm t2, AlgebraTerm t2Type) {
    AlgebraTerm condition = AlgebraFunctionApplication.create(this.cTrue);
    return this.proveEquivalenceUnderCondition(t1, t1Type, t2, t2Type, condition);
    }

    /** Returns true if equivalence of t1 and t2 could be prooved
     *  under condition.
     */
    public boolean proveEquivalenceUnderCondition(AlgebraTerm t1, AlgebraTerm t1Type, AlgebraTerm t2, AlgebraTerm t2Type, AlgebraTerm condition) {

       Vector<RewriteCalculusPair> rwpairs = new Vector<RewriteCalculusPair>();
    Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();

    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    args.add(t1.shallowcopy());
    args.add(t2.shallowcopy());

    DefFunctionSymbol eq = this.getEqualFunction(t1Type);
    AlgebraTerm term = AlgebraFunctionApplication.create(eq, args);
    rwpairs.add(new RewriteCalculusPair(condition, term));
    Vector<AlgebraTerm> rwpairTermsTypes = new Vector<AlgebraTerm>();
    rwpairTermsTypes.add(TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(eq).getTypeMatrix()));
    rwpairsTermsTypes.add(rwpairTermsTypes);
    boolean b = this.prove(rwpairs, rwpairsTermsTypes);
    return b;
    }

    /** Returns true if equivalence of defindeness of t1 and t2 could
     *  be proved under condition.
     */
    public boolean proveDefEquivalenceUnderCondition(AlgebraTerm t1, AlgebraTerm t1Type, AlgebraTerm t2, AlgebraTerm t2Type, AlgebraTerm condition) {
    Vector<RewriteCalculusPair> rwpairs = new Vector<RewriteCalculusPair>();
    Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();

    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    Vector<AlgebraTerm> defargs = new Vector<AlgebraTerm>();
    defargs.add(t1.shallowcopy());

    DefFunctionSymbol def = (DefFunctionSymbol)this.definedChecks.get(t1Type.getSymbol().getName());

    args.add(AlgebraFunctionApplication.create(def, defargs));
    defargs = new Vector<AlgebraTerm>();
    defargs.add(t2.shallowcopy());

    def = (DefFunctionSymbol)this.definedChecks.get(t2Type.getSymbol().getName());

    args.add(AlgebraFunctionApplication.create(def, defargs));

    DefFunctionSymbol eq = this.getEqualFunction(this.boolTypeDef.getDefTerm());

    AlgebraTerm term = AlgebraFunctionApplication.create(eq, args);
    rwpairs.add(new RewriteCalculusPair(condition, term));
    Vector<AlgebraTerm> rwpairTermsTypes = new Vector<AlgebraTerm>();
    rwpairTermsTypes.add(TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(eq).getTypeMatrix()));
    rwpairsTermsTypes.add(rwpairTermsTypes);
    return this.prove(rwpairs, rwpairsTermsTypes);
    }

    public Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>> proveStep(RewriteCalculusPair rwpair, Vector<AlgebraTerm> rwpairTermsTypes) {
    if (rwpair.isTrue() || rwpair.conditionIsFalse()) {
        Vector results = new Vector();
        Vector<Vector<Vector<AlgebraTerm>>> resultsTermsTypes = new Vector<Vector<Vector<AlgebraTerm>>>();
        Vector<RewriteCalculusPair> rwpairs = new Vector<RewriteCalculusPair>();
        Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();
        results.add(rwpairs);
        resultsTermsTypes.add(rwpairsTermsTypes);
        return new Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>>(results, resultsTermsTypes);
    }
    if (this.limitRewriteCalculusPair(rwpair, 3)) {
        Vector<RewriteCalculusPair> rwpairs = new Vector<RewriteCalculusPair>();
        Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();
        rwpairs.add(rwpair);
        rwpairsTermsTypes.add(rwpairTermsTypes);
        Vector results = new Vector();
        Vector<Vector<Vector<AlgebraTerm>>> resultsTermsTypes = new Vector<Vector<Vector<AlgebraTerm>>>();
        results.add(rwpairs);
        resultsTermsTypes.add(rwpairsTermsTypes);
        return new Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>>(results, resultsTermsTypes);
    }
    return this.caseAnalyses(rwpair, rwpairTermsTypes);
    }

    public Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>> prove(RewriteCalculusPair rwpair, Vector<AlgebraTerm> rwpairTermsTypes) {
    boolean changed = false;
    while (true) {
        if (rwpair.isTrue() || rwpair.conditionIsFalse()) {
        Vector<RewriteCalculusPair> rwpairs = new Vector<RewriteCalculusPair>();
        Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();
        Vector results = new Vector();
        Vector<Vector<Vector<AlgebraTerm>>> resultsTermsTypes = new Vector<Vector<Vector<AlgebraTerm>>>();
        results.add(rwpairs);
        resultsTermsTypes.add(rwpairsTermsTypes);
        return new Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>>(results, resultsTermsTypes);
        }
        if (this.limitRewriteCalculusPair(rwpair, 3)) {
        changed = true;
        continue;
        }
        Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>> resultsAndTermsTypes = this.caseAnalyses(rwpair, rwpairTermsTypes);
        if (!resultsAndTermsTypes.x.isEmpty()) {
        return resultsAndTermsTypes;
        }
        if (changed) {
        Vector<RewriteCalculusPair> rwpairs = new Vector<RewriteCalculusPair>();
        Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();
        rwpairs.add(rwpair);
        rwpairsTermsTypes.add(rwpairTermsTypes);
        Vector results = new Vector();
        Vector<Vector<Vector<AlgebraTerm>>> resultsTermsTypes = new Vector<Vector<Vector<AlgebraTerm>>>();
        results.add(rwpairs);
        resultsTermsTypes.add(rwpairsTermsTypes);
        return new Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>>(results, resultsTermsTypes);
        }
        break;
    }
    return new Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>>(new Vector(), new Vector<Vector<Vector<AlgebraTerm>>>());
    }

    public boolean prove(Vector<RewriteCalculusPair> rwpairs, Vector<Vector<AlgebraTerm>> rwpairsTermsTypes) {
    Vector<Pair<Vector<RewriteCalculusPair>,Vector<Vector<AlgebraTerm>>>> fifo = new Vector<Pair<Vector<RewriteCalculusPair>,Vector<Vector<AlgebraTerm>>>>();
    Iterator it = rwpairs.iterator();
    while (it.hasNext()) {
        ((RewriteCalculusPair)it.next()).label();
    }
    fifo.add(new Pair<Vector<RewriteCalculusPair>,Vector<Vector<AlgebraTerm>>>(rwpairs, rwpairsTermsTypes));
    while (!fifo.isEmpty()) {
        Pair<Vector<RewriteCalculusPair>,Vector<Vector<AlgebraTerm>>> rwpairsAndTermsTypes = fifo.remove(0);
        rwpairs = rwpairsAndTermsTypes.x;
        rwpairsTermsTypes = rwpairsAndTermsTypes.y;
        if (rwpairs.isEmpty()) {
        return true;
        }
        RewriteCalculusPair rwpair = (RewriteCalculusPair)rwpairs.remove(0);
        Vector<AlgebraTerm> rwpairTermsTypes = rwpairsTermsTypes.remove(0);
        Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>> replacementsAndTermsTypes = this.prove(rwpair, rwpairTermsTypes);
        Vector replacements = replacementsAndTermsTypes.x;
        Vector<Vector<Vector<AlgebraTerm>>> replacementsTermsTypes = replacementsAndTermsTypes.y;
        boolean mkdeepcopy = false;
        it = replacements.iterator();
        Iterator<Vector<Vector<AlgebraTerm>>> it_replacementsTermsTypes = replacementsTermsTypes.iterator();
        while (it.hasNext()) {
        Vector<RewriteCalculusPair> newrwpairs = (Vector<RewriteCalculusPair>)it.next();
        Vector<Vector<AlgebraTerm>> newrwpairsTermsTypes = it_replacementsTermsTypes.next();
        Vector<RewriteCalculusPair> nextrwpairs = new Vector<RewriteCalculusPair>();
        Vector<Vector<AlgebraTerm>> nextrwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();
        Iterator rwp_it = rwpairs.iterator();
        Iterator<Vector<AlgebraTerm>> it_rwpTermsTypes = rwpairsTermsTypes.iterator();
        while (rwp_it.hasNext()) {
            RewriteCalculusPair oldrwpair = (RewriteCalculusPair)rwp_it.next();
            Vector<AlgebraTerm> oldrwpairTermsTypes = it_rwpTermsTypes.next();
            nextrwpairs.add(mkdeepcopy ? oldrwpair.deepcopy() : oldrwpair);
            Vector<AlgebraTerm> oldrwpairTermsTypesDeepcopy = new Vector<AlgebraTerm>();
            if (mkdeepcopy) {
                oldrwpairTermsTypesDeepcopy.addAll(oldrwpairTermsTypes);
            }
            nextrwpairsTermsTypes.add(mkdeepcopy ? oldrwpairTermsTypesDeepcopy : oldrwpairTermsTypes);
        }
        nextrwpairs.addAll(newrwpairs);
        nextrwpairsTermsTypes.addAll(newrwpairsTermsTypes);
        if (nextrwpairs.isEmpty()) {
            return true;
        }
        fifo.insertElementAt(new Pair<Vector<RewriteCalculusPair>,Vector<Vector<AlgebraTerm>>>(nextrwpairs, nextrwpairsTermsTypes) , 0);
        mkdeepcopy = true;
        }
    }
    return false;
    }

    public boolean proveUnderCondition(AlgebraTerm term, AlgebraTerm termType, AlgebraTerm condition) {
    Vector<RewriteCalculusPair> rwpairs = new Vector<RewriteCalculusPair>();
    rwpairs.add(new RewriteCalculusPair(condition, term));
    Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();
    Vector<AlgebraTerm> rwpairTermTypes = new Vector<AlgebraTerm>();
    rwpairTermTypes.add(termType);
    rwpairsTermsTypes.add(rwpairTermTypes);
    return this.prove(rwpairs, rwpairsTermsTypes);
    }


    /* Helpers */

    protected DefFunctionSymbol getEqualFunction(AlgebraTerm type) {
        String name = "equal_" + type.getSymbol().getName();
        DefFunctionSymbol eq = this.prog.getDefFunctionSymbol(name);
        if (eq == null) {
            eq = this.prog.getPredefFunctionSymbol(name);
        }
        return eq;
    }


    protected AlgebraTerm termReplace(AlgebraTerm term, Hashtable replacements) {
    AlgebraTerm replacement = (AlgebraTerm)replacements.get(term);
    if (replacement != null) {
        return replacement;
    }
    if (term.isVariable()) {
        return term;
    }
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    List<AlgebraTerm> args = term.getArguments();
    Iterator it = args.iterator();
    while (it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        newargs.add(this.termReplace(arg, replacements));
    }
    return AlgebraFunctionApplication.create((SyntacticFunctionSymbol)term.getSymbol(), newargs);
    }

    /** Gets a list of selectors belonging to the constructor csym,
     *  puts them with their rules into this.defsrules and returns
     *  the selectorlist.
     */
    protected List<DefFunctionSymbol> getSelectors(ConstructorSymbol csym) {
    List<DefFunctionSymbol> selectors = csym.getSelectors();
    Iterator it = selectors.iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        if (this.defsrules.get(fsym) == null) {
        this.defsrules.put(fsym, this.prog.getRules(fsym));
        }
    }
    return selectors;
    }

    protected boolean definednessFollows(AlgebraTerm cond, AlgebraSubstitution sub) {
    List<AlgebraTerm> subterms = cond.getAllSubterms();
    Vector range = new Vector(sub.getMapping().values());
    while (!range.isEmpty()) {
        AlgebraTerm t = (AlgebraTerm)range.remove(0);
        if (t.isVariable() || subterms.contains(t)) {
        continue;
        }
        Symbol sym = t.getSymbol();
        if (sym instanceof ConstructorSymbol || ((DefFunctionSymbol)sym).getTermination()) {
        range.addAll(t.getArguments());
        continue;
        }
        return false;
    }
    return true;
    }

    /** Returns true if it can show the definedness of t1 follows from
     *  the definedness of t2.
     */
    protected boolean definednessFollows(AlgebraTerm t1, AlgebraTerm t2) {
    List<AlgebraTerm> subterms = t2.getAllSubterms();
    Vector fifo = new Vector();
    fifo.add(t1);
    while (!fifo.isEmpty()) {
        AlgebraTerm t = (AlgebraTerm)fifo.remove(0);
        if (t.isVariable() || subterms.contains(t)) {
        continue;
        }
        Symbol sym = t.getSymbol();
        if (sym instanceof ConstructorSymbol || ((DefFunctionSymbol)sym).getTermination()) {
        fifo.addAll(t.getArguments());
        continue;
        }
        return false;
    }
    return true;
    }

    protected Set<Rule> getRules(DefFunctionSymbol fsym) {
    Set<Rule> rules = (Set<Rule>)this.defsrules.get(fsym);
    if (rules == null) {
        rules = this.prog.getRules(fsym);
        this.defsrules.put(fsym, rules);
    }
    return rules;
    }

}
