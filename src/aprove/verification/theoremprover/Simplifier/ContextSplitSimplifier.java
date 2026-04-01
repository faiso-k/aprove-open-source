package aprove.verification.theoremprover.Simplifier;

import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

@NoParams
public class ContextSplitSimplifier extends SimplifierProcessor {

    protected Hashtable constructorLifts;
    protected Hashtable<DefFunctionSymbol,Set<Rule>> constructorLiftRules;
    protected Hashtable reflexivePosition;
    protected Hashtable leftneutrals;
    protected Hashtable rightneutrals;
    protected Vector contextSplitInfo;

    private SimplifierObligation obl;

    public ContextSplitSimplifier(){
        super("Context Split Simplifier","CS","Context Split");
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation oobl) {
        this.constructorLifts = new Hashtable();
    this.constructorLiftRules = new Hashtable<DefFunctionSymbol,Set<Rule>>();
    this.reflexivePosition = new Hashtable();
    this.leftneutrals = new Hashtable();
    this.rightneutrals = new Hashtable();
        this.obl = oobl.shallowcopy();
        this.contextSplitInfo = new Vector();
        if (this.contextSplit()) {
           this.setProof(new ContextSplitProof(oobl,this.contextSplitInfo,this.obl));
           this.contextSplitInfo = new Vector();
           return this.obl;
        }
        this.contextSplitInfo = new Vector();
        return null;
    }

    public boolean contextSplit() {
    boolean changed = false;
    Vector lifo = new Vector(this.obl.defs);
    while (!lifo.isEmpty()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)lifo.remove(0);
        DefFunctionSymbol fnsym = this.contextSplit(fsym);
        if (fnsym != null) {
        changed = true;
        lifo.insertElementAt(fnsym, 0);
        }
    }
    return changed;
    }

    public DefFunctionSymbol contextSplit(DefFunctionSymbol fsym) {
    int arity = fsym.getArity();
    for (int i=0; i<arity; i++) {
        DefFunctionSymbol fnsym = this.contextSplit(fsym, i);
        if (fnsym != null) {
                this.contextSplitInfo.add(new Object[]{fsym,Integer.valueOf(i),fnsym});
        //this.symbolicEvaluation();
        return fnsym;
        }
    }
    return null;
    }

    public DefFunctionSymbol contextSplit(DefFunctionSymbol fsym, int pos) {

        AlgebraTerm fsymTypeM = this.obl.typeContext.getSingleTypeOf(fsym).getTypeMatrix();

        AlgebraTerm fsymResType = TypeTools.getResultTerm(fsymTypeM);
        AlgebraTerm fsymArgPosType = TypeTools.getFunctionArgAt(fsymTypeM,pos);

        // TODO remove me
//        assert (!(fsym.getSort().equals(fsym.getArgSort(pos)) ^ fsymResType.equals(fsymArgPosType)));

        if (!fsymResType.equals(fsymArgPosType)) {
            return null;
        }

    Set<Rule> rules = new LinkedHashSet<Rule>((Set<Rule>)this.obl.defsrules.get(fsym));
    // Check that y (the posth argument of the lhs) is a
    // variable and does not occur in any condition.
    Iterator r_it = rules.iterator();
    while (r_it.hasNext()) {
        Rule rule = (Rule)r_it.next();
        AlgebraTerm yt = rule.getLeft().getArgument(pos);
        if (!yt.isVariable()) {
        return null;
        }
        Iterator c_it = rule.getConds().iterator();
        while (c_it.hasNext()) {
        Rule cond = (Rule)c_it.next();
        if (cond.getLeft().getVars().contains(yt)) {
            return null;
        }
        }
    }
    Vector<Rule> lifted = new Vector<Rule>();
    Vector<AlgebraTerm> conditions = new Vector<AlgebraTerm>();
    AlgebraTerm q = null;
    Vector<AlgebraTerm> rs = new Vector<AlgebraTerm>();
    int n = rules.size();
    for (int i=0; i<n; i++) {
        rs.add(null);
    }
    this.obl.liftRules(rules, lifted, conditions);
    AlgebraVariable y = (AlgebraVariable)lifted.get(0).getLeft().getArgument(pos);
    AlgebraTerm yTypeM = this.obl.typeContext.getSingleTypeOf(lifted.get(0).getLeft().getSymbol()).getTypeMatrix();
    AlgebraTerm yType = TypeTools.getFunctionArgAt(yTypeM, pos);
    Sort s = y.getSort();
    String x1name = this.obl.symbnames.getFreshName("x1", false);
    VariableSymbol x2sym = VariableSymbol.create(this.obl.symbnames.getFreshName("x2", false), y.getSort());

    AlgebraTerm x2symType = fsymArgPosType;

    AlgebraSubstitution x2sub = AlgebraSubstitution.create();
    x2sub.put((VariableSymbol)y.getSymbol(), AlgebraVariable.create(x2sym));
    Iterator lr_it = lifted.iterator();
    AlgebraTerm genleft = ((Rule)lr_it.next()).getLeft();
    lr_it = lifted.iterator();
    for (int i=0; lr_it.hasNext(); i++) {
        Rule lrule = (Rule)lr_it.next();
        AlgebraTerm t = lrule.getRight();
        if (t.getSymbol().equals(fsym)) {
        t = t.getArgument(pos);
        }
        if (!t.equals(y)) {
        Set<Position> pis = new HashSet<Position>();
        ContextSplitSimplifier.determineSplitPositions(t, y, Position.create(), pis);
        if (pis.isEmpty() || pis.contains(Position.create())) {
            return null;
        }
        Iterator pi_it = pis.iterator();
        Position pi = (Position)pi_it.next();
        AlgebraTerm t1 = t.getSubterm(pi);
        while (pi_it.hasNext()) {
            pi = (Position)pi_it.next();
            AlgebraTerm t2 = t.getSubterm(pi);
            if (!t1.equals(t2)) {
            return null;
            }
        }
        rs.set(i, t1);
        VariableSymbol x1sym = VariableSymbol.create(x1name, t1.getSymbol().getSort());
        AlgebraTerm ttmp = t;
        pi_it = pis.iterator();
        while (pi_it.hasNext()) {
            pi = (Position)pi_it.next();
            ttmp = ttmp.replaceAt(AlgebraVariable.create(x1sym), pi);
        }
        if (q != null) {
            if ((!q.equals(ttmp.apply(x2sub))) || this.obl.gotDependencies(ttmp, fsym)) {
            return null;
            }
        }
        else {
            q = ttmp.apply(x2sub);
        }
        }
    }
    if (q == null || q.isVariable()) {
        return null;
    }
    VariableSymbol x1sym = null;
    AlgebraTerm x1symType = null;
    int x2occured = -1;
    Iterator arg_it = q.getArguments().iterator();
    Iterator<AlgebraTerm> argType_it = TypeTools.getFunctionArgs(this.obl.typeContext.getSingleTypeOf(q.getSymbol()).getTypeMatrix()).iterator();
    for (int i=0; arg_it.hasNext(); i++) {
        AlgebraTerm arg = (AlgebraTerm)arg_it.next();
        AlgebraTerm argType = argType_it.next();
        if (arg.getSymbol().equals(x2sym)) {
        if (x2occured != -1) {
            return null;
        }
        x2occured = i;
        }
        else {
        if (!arg.getSymbol().getName().equals(x1name)) {
            return null;
        }
        else {
            if (x1sym == null) {
            x1sym = (VariableSymbol)arg.getSymbol();
            x1symType = argType;
            }
        }
        }
    }
    if (x2occured == -1) {
        return null;
    }
    SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)q.getSymbol();
    AlgebraTerm origq = q;
    DefFunctionSymbol cpsym = null;
    AlgebraTerm lneutral = null;
    AlgebraTerm rneutral = null;

    if (!x1symType.equals(x2symType)) {
        // Lifting constructor to get suitable sort.
        if (gsym instanceof ConstructorSymbol) {
//        if (s.getWitnessTerm().getSymbol().equals(gsym)) {
//            return null;
//        }
        if (this.obl.typeContext.getTypeDefOfRootTypeCons(yType).getWitnessTerm().getSymbol().equals(gsym)) {
            return null;
        }
        cpsym = this.getConstructorLift((ConstructorSymbol)gsym);
        if (cpsym == null) {
            return null;
        }
        x1sym = VariableSymbol.create(x1sym.getName(), s);
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(AlgebraVariable.create(x1sym));
        args.add(AlgebraVariable.create(x2sym));
        q = AlgebraFunctionApplication.create(cpsym, args);
        Vector<AlgebraTerm> nrs = new Vector<AlgebraTerm>();
        r_it = rs.iterator();
        for (int i=0; r_it.hasNext(); i++) {
            AlgebraTerm r = (AlgebraTerm)r_it.next();
            if (r != null) {
            nrs.add(this.constructorLift((ConstructorSymbol)gsym, r));
            }
            else {
            nrs.add(null);
            }
        }
        rs = nrs;
        lneutral = (AlgebraTerm)this.leftneutrals.get(cpsym);
        rneutral = (AlgebraTerm)this.rightneutrals.get(cpsym);
        }
        else {
        return null;
        }
    }
    else {
        // Check whether there is a function c' such that q[x1,x2] is equal.
        TypeDefinition x1symTD = this.obl.typeContext.getTypeDef(x1symType.getSymbol().getName());

        Iterator<Symbol> x1Cons_it = x1symTD.getDeclaredSymbols().iterator();

        while (cpsym == null && x1Cons_it.hasNext()) {
        ConstructorSymbol csym = (ConstructorSymbol)x1Cons_it.next();
        cpsym = this.getConstructorLift(csym);
        if (cpsym != null) {
            if (this.termCorrespondsToFunction(q, cpsym, x1sym, x2sym)) {
            lneutral = (AlgebraTerm)this.leftneutrals.get(cpsym);
            rneutral = (AlgebraTerm)this.rightneutrals.get(cpsym);
            }
            else {
            cpsym = null;
            }
        }
        }
        if (cpsym == null) {
        return null;
        }
    }
    // Replace some stuff to make context split applicable
    AlgebraSubstitution sub_x1_lneutral = AlgebraSubstitution.create();
    sub_x1_lneutral.put(x1sym, lneutral);
    Set<Rule> newrules = new HashSet<Rule>();
    r_it = rules.iterator();
    for (int i=0; r_it.hasNext(); i++) {
        Rule rule = ((Rule)r_it.next()).deepcopy();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm right = rule.getRight();
        AlgebraTerm yt = left.getArgument(pos);
        AlgebraSubstitution sub_x2_y = AlgebraSubstitution.create();
        sub_x2_y.put(x2sym, yt);
        try {
        AlgebraSubstitution sub = genleft.matches(left);
        AlgebraTerm newright = right;
        if (right.getSymbol().equals(fsym)) {
            AlgebraTerm r = rs.get(i);
            if (r != null) {
            AlgebraSubstitution sub_x1_ri = AlgebraSubstitution.create();
            sub_x1_ri.put(x1sym, r.apply(sub));
            Vector<AlgebraTerm> args = new Vector<AlgebraTerm>(right.getArguments());
            args.set(pos, q.apply(sub_x1_ri).apply(sub_x2_y));
            newright = AlgebraFunctionApplication.create(fsym, args);
            }
        }
        else if (right.equals(yt)) {
            newright = q.apply(sub_x1_lneutral).apply(sub_x2_y);
        }
        else {
            try {
            AlgebraSubstitution subq = origq.matches(right);
            subq.put(x2sym, yt);
            newright = right.apply(subq);
            }
            catch (UnificationException e) { }
        }
        newrules.add(Rule.create(rule.getConds(), left, newright));
        }
        catch (UnificationException e) { }
    }
    // Create the new function.
    String name = this.obl.symbnames.getFreshName(fsym.getName(), false);

    // TODO removal of sorts
    Vector<Sort> argsorts = new Vector<Sort>(fsym.getArgSorts());
    argsorts.remove(pos);

    Vector<AlgebraTerm> argTypes = new Vector<AlgebraTerm>(TypeTools.getFunctionArgs(fsymTypeM));
    argTypes.remove(pos);

    DefFunctionSymbol fnsym = DefFunctionSymbol.create(name, argsorts, fsym.getSort());
    this.obl.typeContext.setSingleTypeOf(fnsym, new Type(TypeTools.function(argTypes,fsymResType)));

    Set<Rule> fnrules = new HashSet<Rule>();
    r_it = newrules.iterator();
    while (r_it.hasNext()) {
        Rule rule = (Rule)r_it.next();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm right = rule.getRight();
        AlgebraTerm newright = null;
        AlgebraTerm yt = left.getArgument(pos);
        if (right.getSymbol().equals(fsym)) {
        AlgebraTerm posarg = right.getArgument(pos);
        if (posarg.equals(yt)) {
            Vector<AlgebraTerm> args = new Vector<AlgebraTerm>(right.getArguments());
            args.remove(pos);
            newright = AlgebraFunctionApplication.create(fnsym, args);
        }
        else {
            try {
            AlgebraSubstitution sub1 = q.matches(posarg);
            if (!sub1.get(x2sym).equals(yt)) {
                return null;
            }
            Vector<AlgebraTerm> args = new Vector<AlgebraTerm>(right.getArguments());
            args.remove(pos);
            AlgebraSubstitution sub2 = AlgebraSubstitution.create();
            sub2.put(x1sym, AlgebraFunctionApplication.create(fnsym, args));
            sub2.put(x2sym, sub1.get(x1sym));
            newright = q.apply(sub2);
            }
            catch (UnificationException e) {
            return null;
            }
        }
        }
        else {
        try {
            AlgebraSubstitution sub1 = q.matches(right);
            if (!sub1.get(x2sym).equals(yt)) {
            return null;
            }
            newright = sub1.get(x1sym);
        }
        catch (UnificationException e) {
            return null;
        }
        }
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>(left.getArguments());
        args.remove(pos);
        AlgebraTerm newleft = AlgebraFunctionApplication.create(fnsym, args);
        fnrules.add(Rule.create(rule.getConds(), newleft, newright));
    }
    this.obl.defsrules.put(fnsym, fnrules);
    this.obl.defs.add(fnsym);
    this.obl.updateSymbol(fnsym, fnrules);
    // Change rules of the original f to use f'.
    newrules = new HashSet<Rule>();
    Vector<AlgebraTerm> xs = new Vector<AlgebraTerm>();

    // TODO removal of sorts
    Iterator<Sort> s_it = fsym.getArgSorts().iterator();
    for(int i=0; i<fsym.getArity(); ++i) {
        s = s_it.next();
        name = this.obl.symbnames.getFreshName("x_"+i, false);
        xs.add(AlgebraVariable.create(VariableSymbol.create(name, s)));
    }

    AlgebraTerm left = AlgebraFunctionApplication.create(fsym, xs);
    Vector<AlgebraTerm> xns = new Vector<AlgebraTerm>(xs);
    AlgebraTerm yt = xns.remove(pos);
    AlgebraSubstitution sub = AlgebraSubstitution.create();
    sub.put(x1sym, AlgebraFunctionApplication.create(fnsym, xns));
    sub.put(x2sym, yt);
    AlgebraTerm right = q.apply(sub);
    newrules.add(Rule.create(left, right));
    this.obl.defsrules.put(fsym, newrules);
    this.obl.updateSymbol(fsym, newrules);
    if (rneutral != null) {
        // First rewrite with f(x*,y) -&gt; q[f'(x*),y],
        // then rewrite with q[x,rneutral] -&gt; x in every rule.
        sub = AlgebraSubstitution.create();
        sub.put(x2sym, rneutral);
        AlgebraVariable x1 = AlgebraVariable.create(x1sym);
        AlgebraTerm qn = q.apply(sub);
        Iterator h_it = (new Vector(this.obl.defsrules.keySet())).iterator();
        while (h_it.hasNext()) {
        DefFunctionSymbol hsym = (DefFunctionSymbol)h_it.next();
        int sig = hsym.getSignatureClass();
        if (sig == Symbol.MAINSIG || (!this.obl.isProjection(hsym) && sig == Symbol.DEFAULTSIG)) {
            newrules = new HashSet<Rule>();
            r_it = ((Set)this.obl.defsrules.get(hsym)).iterator();
            while (r_it.hasNext()) {
            Rule rule = (Rule)r_it.next();
            newrules.add(ContextSplitSimplifier.rewrite(ContextSplitSimplifier.rewrite(rule, left, right), qn, x1));
            }
            this.obl.defsrules.put(hsym, newrules);
            this.obl.updateSymbol(hsym, newrules);
        }
        }
    }
    return fnsym;
    }

    /** Rewrites lhs of the conditions and the rhs according to
     *  an unconditional rewrite rule left to right.
     */
    protected static Rule rewrite(Rule rule, AlgebraTerm left, AlgebraTerm right) {
    Vector<Rule> newconds = new Vector<Rule>();
    Iterator c_it = rule.getConds().iterator();
    while (c_it.hasNext()) {
        Rule cond = (Rule)c_it.next();
        newconds.add(Rule.create(ContextSplitSimplifier.rewrite(cond.getLeft(), left, right), cond.getRight()));
    }
    return Rule.create(newconds, rule.getLeft(), ContextSplitSimplifier.rewrite(rule.getRight(), left, right));
    }

    /** Rewrites a term accordint to an unconditional rewrite rule
     *  left to right.
     */
    protected static AlgebraTerm rewrite(AlgebraTerm t, AlgebraTerm left, AlgebraTerm right) {
    if (t.isVariable()) {
        return t;
    }
    SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)t.getSymbol();
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    Iterator a_it = t.getArguments().iterator();
    while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        newargs.add(ContextSplitSimplifier.rewrite(arg, left, right));
    }
    t = AlgebraFunctionApplication.create(fsym, newargs);
    try {
        AlgebraSubstitution sigma = left.matches(t);
        t = right.apply(sigma);
    }
    catch (UnificationException e) { }
    return t;
    }

    /** Determine all positions pi where t.subterm(pi) does
     * not contain y, but all positions pi' above pi contain y.
     */
    private static boolean determineSplitPositions(AlgebraTerm t, AlgebraVariable y, Position pi, Set<Position> pis) {
    if (t.equals(y)) {
        return true;
    }
    if (t.isVariable()) {
        return false;
    }
    Vector candidates = new Vector();
    boolean containsy = false;
    Iterator it = t.getArguments().iterator();
    for (int i=0; it.hasNext(); i++) {
        AlgebraTerm s = (AlgebraTerm)it.next();
        Position pi2 = pi.shallowcopy();
        pi2.add(i);
        if (ContextSplitSimplifier.determineSplitPositions(s, y, pi2, pis)) {
        containsy = true;
        }
        else {
        candidates.add(pi2);
        }
    }
    if (containsy) {
        pis.addAll(candidates);
    }
    return containsy;
    }

    protected DefFunctionSymbol getConstructorLift(ConstructorSymbol csym) {
    DefFunctionSymbol cpsym = (DefFunctionSymbol)this.constructorLifts.get(csym);
    if (cpsym != null) {
        this.obl.defsrules.put(cpsym, this.constructorLiftRules.get(cpsym));
        return cpsym;
    }
    Integer pos = (Integer)this.reflexivePosition.get(csym);
    if (pos != null) {
        return null;
    }
    // Create function-symbol.

    // TODO removal of sorts
    Sort sort = csym.getSort();

    AlgebraTerm csymTypeM = this.obl.typeContext.getSingleTypeOf(csym).getTypeMatrix();
    AlgebraTerm csymResType = TypeTools.getResultTerm(csymTypeM);

    // TODO removal of sorts
    int i = -1;
    Iterator s_it = csym.getArgSorts().iterator();
    Iterator<AlgebraTerm> csymArgType_it = TypeTools.getFunctionArgs(csymTypeM).iterator();
    for (int j=0; (i == -1) && csymArgType_it.hasNext(); j++) {
        AlgebraTerm csymArgType = csymArgType_it.next();
        Sort s = (Sort)s_it.next();
//        if (s.equals(sort)) {
        if (csymArgType.equals(csymResType)) {
        i = j;
        }
    }
    if (i == -1) {
        return null;
    }
    // TODO removal of sorts
    List<Sort> argsorts = new Vector<Sort>();
    argsorts.add(sort);
    argsorts.add(sort);

    Vector<AlgebraTerm> argTypes = new Vector<AlgebraTerm>();
    argTypes.add(csymResType);
    argTypes.add(csymResType);

    String name = this.obl.symbnames.getFreshName(csym.getName()+"_"+i, false);
    cpsym = DefFunctionSymbol.create(name, argsorts, sort);

    AlgebraTerm wt = this.obl.typeContext.getTypeDef(csymResType.getSymbol().getName()).getWitnessTerm();

    if (wt.getSymbol().equals(csym)) {
        return null;
    }

    this.obl.typeContext.setSingleTypeOf(cpsym, new Type(TypeTools.function(argTypes, csymResType)));

    this.leftneutrals.put(cpsym, wt);
    Set<Rule> rules = new HashSet<Rule>();

    // TODO removal of sorts
//    boolean rneutral_implied = sort.getConstructorSymbols().size() == 2;
//    Iterator c_it = sort.getConstructorSymbols().iterator();

    Set<Symbol> csymResTypeConstructors = this.obl.typeContext.getTypeDefOfRootTypeCons(csymResType).getDeclaredSymbols();
    boolean rneutral_implied = csymResTypeConstructors.size() == 2;
    Iterator<Symbol> c_it = csymResTypeConstructors.iterator();

    while (c_it.hasNext()) {
        ConstructorSymbol dsym = (ConstructorSymbol)c_it.next();
        Vector<AlgebraTerm> xs = new Vector<AlgebraTerm>();

        // TODO removal of sorts
        Iterator<Sort> so_it = dsym.getArgSorts().iterator();

        for (int j=0; j< dsym.getArity(); j++) {

            // TODO removal of sorts
            Sort s = so_it.next();

            name = this.obl.symbnames.getFreshName("x_"+j, false);
            xs.add(AlgebraVariable.create(VariableSymbol.create(name, s)));
        }
        name = this.obl.symbnames.getFreshName("y", false);
        AlgebraVariable y = AlgebraVariable.create(VariableSymbol.create(name, sort));
        List<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(AlgebraFunctionApplication.create(dsym, xs));
        args.add(y.deepcopy());
        AlgebraTerm left = AlgebraFunctionApplication.create(cpsym, args);
        AlgebraTerm right;
        if (dsym.equals(csym)) {
        // Create rule c'(c(x_1,...,x_n),y) -> c(x_1,...,c'(x_i,y),...,x_n).
        Vector<AlgebraTerm> rargs = new Vector<AlgebraTerm>();
        Iterator x_it = xs.iterator();
        for (int j=0; x_it.hasNext(); j++) {
            AlgebraVariable x = (AlgebraVariable)x_it.next();
            if (j==i) {
            args = new Vector<AlgebraTerm>();
            args.add(x.deepcopy());
            args.add(y.deepcopy());
            rargs.add(AlgebraFunctionApplication.create(cpsym, args));
            }
            else {
            rargs.add(x.deepcopy());
            }
        }
        right = AlgebraFunctionApplication.create(csym, rargs);
        }
        else {
        // Create rule c'(d(x_1,...,x_{n_j}),y) -> y.
        right = y.deepcopy();
        if (xs.size() != 0 || !wt.getSymbol().equals(dsym)) {
            rneutral_implied = false;
        }
        }
        rules.add(Rule.create(left, right));
    }
    if (rneutral_implied) {
        this.rightneutrals.put(cpsym, wt);
    }
    this.constructorLifts.put(csym, cpsym);
    this.obl.defsrules.put(cpsym, rules);
    this.obl.defs.add(cpsym);
    this.obl.updateSymbol(cpsym, rules);
    this.constructorLiftRules.put(cpsym, rules);
    this.reflexivePosition.put(csym, Integer.valueOf(i));
    return cpsym;
    }

    /** Returns true if it can be shown that q[x1,x2] corresponds to
     *  f(x1,x2) can be shown.
     */
    private boolean termCorrespondsToFunction(AlgebraTerm q, DefFunctionSymbol fsym, VariableSymbol x1sym, VariableSymbol x2sym) {
    if (!(q.getSymbol() instanceof DefFunctionSymbol)) {
        return false;
    }
    DefFunctionSymbol gsym = (DefFunctionSymbol)q.getSymbol();
    if (gsym.getArity() == 2) {
        Set<Rule> frules = (Set<Rule>)this.obl.defsrules.get(fsym);
        Set<Rule> grules = (Set<Rule>)this.obl.defsrules.get(gsym);
        boolean swap = false;
        if (q.getArgument(0).getSymbol().equals(x2sym)) {
        swap = true;
        }
        Iterator fr_it = frules.iterator();
        while (fr_it.hasNext()) {
        Rule frule = (Rule)fr_it.next();
        AlgebraTerm fleft = frule.getLeft();
        if (!frule.getConds().isEmpty()) {
            return false;
        }
        // Get correspondent rhs in grules.
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(fleft.getArgument(0));
        args.insertElementAt(fleft.getArgument(1), swap ? 0 : 1);
        AlgebraTerm t = AlgebraFunctionApplication.create(gsym, args);
        AlgebraTerm gright = null;
        Iterator gr_it = (new Vector(grules)).iterator();
        while (gright == null && gr_it.hasNext()) {
            Rule grule = (Rule)gr_it.next();
            AlgebraTerm gleft = grule.getLeft();
            try {
            AlgebraSubstitution sub = gleft.matches(t);
            if (!grule.getConds().isEmpty()) {
                return false;
            }
            gright = grule.getRight().apply(sub);
            }
            catch (Exception e) { }
        }
        // Check whether rhs' are equal.
        if (gright == null || !SimplifierObligation.replace_f_with_g(gright, gsym, fsym).equals(frule.getRight())) {
            return false;
        }
        gr_it.remove();
        }
        return true;
    }
    return false;
    }

    private AlgebraTerm constructorLift(ConstructorSymbol csym, AlgebraTerm t) {
    Integer pos = (Integer)this.reflexivePosition.get(csym);
    if (pos == null) {
        return null;
    }
    int j = pos.intValue();
    int n = csym.getArity();
    Vector<AlgebraTerm> ts = new Vector<AlgebraTerm>();
    for (int i=0; i<n; i++) {
        AlgebraTerm csymType = TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(csym).getTypeMatrix());
        TypeDefinition csymTD = this.obl.typeContext.getTypeDef(csymType.getSymbol().getName());

        ts.add(i==j ? csymTD.getWitnessTerm() : t.deepcopy());
    }
    return AlgebraFunctionApplication.create(csym, ts);
    }

}
