package aprove.verification.theoremprover.Simplifier;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Verifier.*;

@NoParams
public class ContextMoveSimplifier extends BasicFixedValueSimplifier {

    public ContextMoveSimplifier(){
        super("Context Move Simplifier","CM","Context Move");
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation oobl) {
        this.obl = oobl.shallowcopy();
        this.resetfvtInfo();
        Map fsym2cmPos = this.contextMove(); // return true if changes occur
        if (!fsym2cmPos.isEmpty()){
            this.setProof(new ContextMoveProof(oobl,fsym2cmPos,this.obl));
            this.resetfvtInfo();
            this.setMessage("Context Move");
            return this.obl;
        }
        this.resetfvtInfo();
        return null;
    }

    /* Context-Moving */

    /** Performs a context-move on a function if possible.
     */
    public Map contextMove() {
        Map fsym2cmPos = new HashMap();
    SimplifierProcessor.log.log(Level.FINER, "Simplifier: Performing context move.\n");
    Hashtable origin = new Hashtable();
    Iterator it = (new Vector(this.obl.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        origin.put(fsym, fsym);
    }
//    Vector fifo = new Vector(this.obl.defs);

    // Ordering according to the numbers.
    // Then all functions occuring on a rhs already have been processed.
    Vector<DefFunctionSymbol> fifo = this.sortByDefFuncNum(this.obl.defs);

    while (!fifo.isEmpty()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)fifo.remove(0);
        int n = fsym.getArity();
            BitSet posSet = new BitSet();
        for (int i=0; i<n; i++) {
        DefFunctionSymbol fnsym = this.contextMove(fsym, origin, i);
        if (fnsym != null) {
            fifo.add(fnsym);
                    posSet.set(i);
        }
        }
            if (!posSet.isEmpty()){
                fsym2cmPos.put(fsym,posSet);
            }
    }
        return fsym2cmPos;
    }

    /** Performs a context-move on the function given by fsym on position
     *  pos.
     */
    public DefFunctionSymbol contextMove(DefFunctionSymbol fsym, Hashtable origin, int pos) {
    Set<Rule> rules = (Set<Rule>)this.obl.defsrules.get(fsym);
    Set<Rule> recrules = new HashSet<Rule>();
    Set<Rule> nonrecrules = new HashSet<Rule>();
    // Split rule into recrules and nonrecrules
    Iterator it = rules.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm right = rule.getRight();
        Symbol lsym = left.getSymbol();
        Symbol rsym = right.getSymbol();
        if (lsym.equals(rsym)) {
        recrules.add(rule);
        }
        else {
        nonrecrules.add(rule);
        }
    }
    if (recrules.isEmpty() || nonrecrules.isEmpty()) {
        return null;
    }
    Vector<Rule> liftrecrules = new Vector<Rule>();
    Vector<AlgebraTerm> recconditions = new Vector<AlgebraTerm>();
    this.obl.liftRules(recrules, liftrecrules, recconditions);
    Vector<Rule> liftnonrecrules = new Vector<Rule>();
    Vector<AlgebraTerm> nonrecconditions = new Vector<AlgebraTerm>();
    this.obl.liftRules(nonrecrules, liftnonrecrules, nonrecconditions);
    // Check left-commutativity
    try {
        if (!this.isLeftCommutative(fsym, pos, this.obl.liftRules(recrules), this.obl.liftRules(nonrecrules))) {
        return null;
        }
    }
    catch (UnificationException e) { // This should not happen.
        return null;
    }
    // Check that y (the pos-th argurment) occurs in every
    // r_i for 1<=i<=m and there is a 1<=i<=k such that r_i != y
    boolean has_different_ri = false;
    it = liftrecrules.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraVariable y = (AlgebraVariable)rule.getLeft().getArgument(pos);
        AlgebraTerm r = rule.getRight().getArgument(pos);
        if (!r.getVars().contains(y)) {
        return null;
        }
        has_different_ri = has_different_ri || !r.equals(y);
    }
    it = liftnonrecrules.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraVariable y = (AlgebraVariable)rule.getLeft().getArgument(pos);
        AlgebraTerm r = rule.getRight();
        if (!r.getVars().contains(y)) {
        return null;
        }
        // removed, since habilGiesl says: "if at least one of the _recursive_ arguments r_i is different from y"
        //has_different_ri = has_different_ri || !r.equals(y);
    }
    if (!has_different_ri) {
        return null;
    }
    // Check that the variable on the lhs at position pos does not
    // occur in arguments of functions which are dependendt on fsym in r.
    // Also split the rules to recrules and nonrecrules.
    it = liftrecrules.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm right = rule.getRight();
        AlgebraVariable v = (AlgebraVariable)left.getArgument(pos);
        AlgebraTerm r = right.getArgument(pos);
        if (this.obl.occursInDependentFunctions(v, fsym, r)) {
        return null;
        }
    }
    it = liftnonrecrules.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm right = rule.getRight();
        AlgebraVariable v = (AlgebraVariable)left.getArgument(pos);
        if (this.obl.occursInDependentFunctions(v, fsym, right)) {
        return null;
        }
    }
    boolean needsParameterDuplication = false;
    // Check that y does not occur in a condition.
    it = liftrecrules.iterator();
    Iterator c_it = recconditions.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraTerm cond = (AlgebraTerm)c_it.next();
        AlgebraVariable v = (AlgebraVariable)rule.getLeft().getArgument(pos);
        if (cond.getVars().contains(v)) {
        needsParameterDuplication = true;
        break;
        }
    }
    if (!needsParameterDuplication) {
        it = liftnonrecrules.iterator();
        c_it = nonrecconditions.iterator();
        while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraTerm cond = (AlgebraTerm)c_it.next();
        AlgebraVariable v = (AlgebraVariable)rule.getLeft().getArgument(pos);
        if (cond.getVars().contains(v)) {
            needsParameterDuplication = true;
            break;
        }
        }
    }
    // Check that y (the variable that is the pos-th argument on the rhs)
    // does not occur in an r*_i 1<=i<=k (e.g. all arguments except the last
    // in the rhs-rule of all rules in recrules).
    int arity = fsym.getArity();
    if (!needsParameterDuplication) {
        it = liftrecrules.iterator();
        while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm right = rule.getRight();
        AlgebraVariable v = (AlgebraVariable)left.getArgument(pos);
        for (int i=0; i<arity; i++) {
            if (i != pos) {
            AlgebraTerm r = right.getArgument(i);
            if (r.getVars().contains(v)) {
                needsParameterDuplication = true;
                break;
            }
            }
        }
        }
    }
    // Check whether the pos-th argument occurs in a condition.
    Iterator r_it = liftrecrules.iterator();
    c_it = recconditions.iterator();
    while (r_it.hasNext()) {
        Rule r = (Rule)r_it.next();
        AlgebraTerm cond = (AlgebraTerm)c_it.next();
        AlgebraVariable v = (AlgebraVariable)r.getLeft().getArgument(pos);
        if (cond.getVars().contains(v)) {
        needsParameterDuplication = true;
        }
    }
    r_it = liftnonrecrules.iterator();
    c_it = nonrecconditions.iterator();
    while (r_it.hasNext()) {
        Rule r = (Rule)r_it.next();
        AlgebraTerm cond = (AlgebraTerm)c_it.next();
        AlgebraVariable v = (AlgebraVariable)r.getLeft().getArgument(pos);
        if (cond.getVars().contains(v)) {
        needsParameterDuplication = true;
        }
    }
    Hashtable origdefsrules = null;
    Set<DefFunctionSymbol> origdefs = null;
    Hashtable origdependencies = null;
    TypeContext origTypeContext = null;
    // May be a paramer-duplication is needed to do the transformation.
    if (needsParameterDuplication) {
        // Save the current state. Maybe we have to undo everything.
        origdefsrules = new Hashtable(this.obl.defsrules);
        origdefs = new HashSet<DefFunctionSymbol>(this.obl.defs);
        origdependencies = new Hashtable(this.obl.dependencies);
        origTypeContext = this.obl.typeContext.deepcopy();
        fsym = this.parameterDuplication(fsym, pos);
        pos++;
    }
    // Everthing is fine. Do the transformation.
    Set<Rule> newrules = new HashSet<Rule>();
    it = ((Set)this.obl.defsrules.get(fsym)).iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm right = rule.getRight();
        List<Rule> conds = rule.getConds();
        if (fsym.equals(right.getSymbol())) {
            AlgebraTerm y = left.getArgument(pos);
            VariableSymbol ysym = (VariableSymbol)y.getSymbol();
            List<AlgebraTerm> args = new Vector<AlgebraTerm>(right.getArguments());
            AlgebraTerm r = args.get(pos);

            if (aprove.Globals.useAssertions) {
                assert r.getVariableSymbols().contains(ysym) : "Term "+r+"does not contain the variable "+ysym+"!";
            }

            args.set(pos, y.deepcopy());
            AlgebraTerm newright = AlgebraFunctionApplication.create(fsym, args);
            AlgebraSubstitution sub = AlgebraSubstitution.create();
            sub.put(ysym, newright);
            newright = r.apply(sub);
            newrules.add(Rule.create(conds, left, newright));
        }
        else {
            newrules.add(rule);
        }
    }
    this.obl.defsrules.put(fsym, newrules);
    this.obl.updateSymbol(fsym, newrules);
    // If we got here by parameter-duplication and the application
    // of the fixed value rule fails, we have to undo everything.
    boolean b = !this.fixedValueTransformation(fsym);
    if (b && needsParameterDuplication) {
        this.obl.dependencies = origdependencies;
        this.obl.defs = origdefs;
        this.obl.defsrules = origdefsrules;
        this.obl.typeContext = origTypeContext;
        return null;
    }
    return fsym;
    }

    /** Checks whether fsym with the rules recrules
     *  and nonrecrules is left-commutative.
     */
    protected boolean isLeftCommutative(DefFunctionSymbol fsym, int pos, Set<Rule> recrules, Set<Rule> nonrecrules) throws UnificationException {
    Iterator it1 = recrules.iterator();
    while (it1.hasNext()) {
        Rule rule1 = (Rule)it1.next();
        Iterator it2 = nonrecrules.iterator();
        while (it2.hasNext()) {
        Rule rule2 = (Rule)it2.next();
        if (!this.isLeftCommutative(fsym, pos, rule1, rule2)) {
            return false;
        }
        }
        it2 = recrules.iterator();
        while (it2.hasNext()) {
        Rule rule2 = (Rule)it2.next();
        if (!this.isLeftCommutative(fsym, pos, rule1, rule2)) {
            return false;
        }
        }
    }
    return true;
    }

    /** Checks whether the rule1, rule2 in fsym are left-commutative.
     */
    protected boolean isLeftCommutative(DefFunctionSymbol fsym, int pos,  Rule rule1, Rule rule2) throws UnificationException {
    // Creating substitutions to assign xs und ys.
    VariableSymbol z = null;
    AlgebraSubstitution xs = AlgebraSubstitution.create();
    AlgebraSubstitution ys = AlgebraSubstitution.create();
    int i = 0;

    // TODO removal of sorts
    Iterator it = fsym.getArgSorts().iterator();

    Iterator a_it = rule1.getLeft().getArguments().iterator();
    while (a_it.hasNext()) {

        // TODO removal of sorts
        Sort s = (Sort)it.next();

        VariableSymbol vsym = (VariableSymbol)((AlgebraTerm)a_it.next()).getSymbol();
        if (i != pos) {
        i++;
        String name = this.obl.symbnames.getFreshName("x_"+i, true);
        AlgebraTerm t = AlgebraVariable.create(VariableSymbol.create(name, s));
        xs.put(vsym, t);
        name = this.obl.symbnames.getFreshName("y_"+i, true);
        t = AlgebraVariable.create(VariableSymbol.create(name, s));
        ys.put(vsym, t);
        }
        else {
        i++;
        String name = this.obl.symbnames.getFreshName("z", true);
        z = VariableSymbol.create(name, s);
        AlgebraTerm t = AlgebraVariable.create(z);
        xs.put(vsym, t);
        ys.put(vsym, t.deepcopy());
        }
    }
    AlgebraSubstitution sub = rule2.getLeft().matches(rule1.getLeft());
    AlgebraTerm r1 = rule1.getRight();
    AlgebraTerm r2 = rule2.getRight().apply(sub);

    // determine whether these are recursive calls (then the pos-th argument has to be taken)
    if (r1.getSymbol().equals(fsym)) {
        r1 = r1.getArgument(pos);
    }
    if (r2.getSymbol().equals(fsym)) {
        r2 = r2.getArgument(pos);
    }


    // r1[x*,r2[y*,z]] and r2[y*,r1[x*,z]] are syntactically equal?
    sub = AlgebraSubstitution.create();
    sub.put(z, r2.apply(ys));
    AlgebraTerm term1 = r1.apply(xs).apply(sub);
    sub = AlgebraSubstitution.create();
    sub.put(z, r1.apply(xs));
    AlgebraTerm term2 = r2.apply(ys).apply(sub);
    if (term1.equals(term2)) {
        return true;
    }
    // No, then check whether f is j-commutative for appropriate j.
    if (!rule1.getRight().equals(rule2.getRight())) {
        return false;
    }
    i = 0;
    int j = -1;
    boolean b = true;
    AlgebraVariable zv = AlgebraVariable.create(z);

    AlgebraTerm r = r2.apply(xs);

    if (r.isVariable()) {
        return false;
    }
    Iterator<AlgebraTerm> arg_it = r.getArguments().iterator();
    while (arg_it.hasNext()) {
        AlgebraTerm t = arg_it.next();
        if (z.equals(t.getSymbol())) {
        if (j<0) {
            j = i;
        }
        else {
            b = false;
            break;
        }
        }
        else {
        if (t.getVars().contains(zv)) {
            b = false;
            break;
        }
        }
        i++;
    }
    if (b && j>=0) {
        if (this.is_jCommutative(r.getSymbol(), j)) {
        return true;
        }
    }
    return false;
    }


    /* Parameter-Duplication */

    /** Creates a new function where the pos-th parameter of fsym is duplicated.
     */
    protected DefFunctionSymbol parameterDuplication(DefFunctionSymbol fsym, int pos) {
    Set<Rule> rules = (Set<Rule>)this.obl.defsrules.get(fsym);

    // TODO removal of sorts
    Vector<Sort> sorts = new Vector<Sort>(fsym.getArgSorts());
    Sort s = sorts.get(pos);
    sorts.insertElementAt(s, pos);

    AlgebraTerm fsymTypeM = this.obl.typeContext.getSingleTypeOf(fsym).getTypeMatrix();
    Vector<AlgebraTerm> argTypes = new Vector<AlgebraTerm>(TypeTools.getFunctionArgs(fsymTypeM));
    argTypes.insertElementAt(argTypes.get(pos), pos);

    String name = this.obl.symbnames.getFreshName(fsym.getName(), false);
    DefFunctionSymbol fnsym = DefFunctionSymbol.create(name, sorts, fsym.getSort());

    this.obl.typeContext.setSingleTypeOf(fnsym, new Type(TypeTools.function(argTypes,TypeTools.getResultTerm(fsymTypeM))));

    Set<Rule> newrules = new HashSet<Rule>();
    name = this.obl.symbnames.getFreshName("x_"+(pos+1), false);
    VariableSymbol vsym = VariableSymbol.create(name, fsym.getArgSort(pos));

    // lifting the rules, so that the replacement is done correctly
    // otherwise it could occur that the newly introduced variable was not introduced everywhere on the rhs,
    // thereby breaking the context move and generating non-recursive rules from recursive ones
    Vector<Rule> liftedRuleVec = new Vector<Rule>();
    Vector<AlgebraTerm> liftedCondVec = new Vector<AlgebraTerm>();
    this.obl.liftRules(rules,liftedRuleVec,liftedCondVec);
    Iterator<Rule> liftedRule_it = liftedRuleVec.iterator();
    Iterator<AlgebraTerm> liftedCond_it = liftedCondVec.iterator();
    rules = new HashSet<Rule>();
    while (liftedRule_it.hasNext()) {
        Rule liftedRule = liftedRule_it.next();
        Rule liftedCond = Rule.create(liftedCond_it.next(),AlgebraFunctionApplication.create(this.obl.cTrue));
        rules.add(Rule.create(Arrays.asList(liftedCond), liftedRule.getLeft(), liftedRule.getRight()));
    }

    Iterator it = rules.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>(rule.getLeft().getArguments());
        AlgebraTerm posarg = args.get(pos);
        Hashtable replacements = new Hashtable();
        AlgebraVariable v = AlgebraVariable.create(vsym);
        args.insertElementAt(v, pos+1);
        Vector<AlgebraTerm> conditions = new Vector<AlgebraTerm>();
        this.obl.getLiftReplacements(posarg, replacements, v, conditions);
        AlgebraTerm newleft = AlgebraFunctionApplication.create(fnsym, args);
        AlgebraTerm newright = rule.getRight();
        newright = this.resolveParameterDuplication(newright, fsym, fnsym, pos, replacements, !fsym.equals(newright.getSymbol()));
        Vector<Rule> newconds = new Vector<Rule>();
        Iterator c_it = rule.getConds().iterator();
        while (c_it.hasNext()) {
        Rule cond = (Rule)c_it.next();
        AlgebraTerm cleft = this.resolveParameterDuplication(cond.getLeft(), fsym, fnsym, pos, replacements, false);
        newconds.add(Rule.create(cleft, cond.getRight()));
        }
        newrules.add(Rule.create(newconds, newleft, newright));
    }
    it = (new Vector(this.obl.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol gsym = (DefFunctionSymbol)it.next();
        if (!fsym.equals(gsym)) {
        this.replaceWithDuplicatedParameterFunction(gsym, fsym, fnsym, pos);
        }
    }
    this.obl.defs.add(fnsym);
    this.obl.defsrules.put(fnsym, newrules);
    this.obl.updateSymbol(fnsym, newrules);
    return fnsym;
    }

    protected AlgebraTerm resolveParameterDuplication(AlgebraTerm term, DefFunctionSymbol fsym, DefFunctionSymbol fnsym, int pos, Hashtable replacements, boolean replace) {
    /* Do replace in the pos-th argument of fnsym. */
    if (replace) {
        AlgebraTerm replacement = (AlgebraTerm)replacements.get(term);
        if (replacement != null) {
        return replacement;
        }
    }
    if (term.isVariable()) {
        return term;
    }
    SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)term.getSymbol();
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    if (gsym.equals(fsym)) {
        Iterator it = term.getArguments().iterator();
        for (int i = 0; it.hasNext(); i++) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        newargs.add(this.resolveParameterDuplication(arg, fsym, fnsym, pos, replacements, replace));
        if (pos == i) {
            newargs.add(this.resolveParameterDuplication(arg.deepcopy(), fsym, fnsym, pos, replacements, true));
        }
        }
        gsym = fnsym;
    }
    else {
        Iterator it = term.getArguments().iterator();
        while (it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        newargs.add(this.resolveParameterDuplication(arg, fsym, fnsym, pos, replacements, replace));
        }
    }
    return AlgebraFunctionApplication.create(gsym, newargs);
    }

    protected void replaceWithDuplicatedParameterFunction(DefFunctionSymbol gsym, DefFunctionSymbol fsym, DefFunctionSymbol fnsym, int pos) {
    Set<Rule> rules = (Set<Rule>)this.obl.defsrules.get(gsym);
    Set<Rule> newrules = new HashSet<Rule>();
    Iterator it = rules.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraTerm newright = this.replaceWithDuplicatedParameterFunction(rule.getRight(), fsym, fnsym, pos);
        List<Rule> newconds = new Vector<Rule>();
        Iterator cond_it = rule.getConds().iterator();
        while (cond_it.hasNext()) {
        Rule cond = (Rule)cond_it.next();
        AlgebraTerm newcondleft = this.replaceWithDuplicatedParameterFunction(cond.getLeft(), fsym, fnsym, pos);
        newconds.add(Rule.create(newcondleft, cond.getRight()));
        }
        newrules.add(Rule.create(newconds, rule.getLeft(), newright));
    }
    this.obl.defsrules.put(gsym, newrules);
    this.obl.updateSymbol(gsym, newrules);
    }

    protected AlgebraTerm replaceWithDuplicatedParameterFunction(AlgebraTerm term, DefFunctionSymbol fsym, DefFunctionSymbol fnsym, int pos) {
    if (term.isVariable()) {
        return term;
    }
    SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)term.getSymbol();
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    if (gsym.equals(fsym)) {
        gsym = fnsym;
        Iterator it = term.getArguments().iterator();
        for (int i=0; it.hasNext(); i++) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        AlgebraTerm newarg = this.replaceWithDuplicatedParameterFunction(arg, fsym, fnsym, pos);
        newargs.add(newarg);
        if (i == pos) {
            newargs.add(newarg.deepcopy());
        }
        }
    }
    else {
        Iterator it = term.getArguments().iterator();
        while (it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        newargs.add(this.replaceWithDuplicatedParameterFunction(arg, fsym, fnsym, pos));
        }
    }
    return AlgebraFunctionApplication.create(gsym, newargs);
    }

    /** Trys to find out whether sym is j-commutative.
     */
    protected boolean is_jCommutative(Symbol sym, int j) {
    if (sym instanceof VariableSymbol) {
        return false;
    }
    SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)sym;
    AlgebraTerm fsymTypeM = this.obl.typeContext.getSingleTypeOf(fsym).getTypeMatrix();

    // j has to be a valid position.
    int arity = fsym.getArity();
    if (arity <= j) {
        return false;
    }
    // The output-type and the type of the j-th argument must be equal.
    if (!TypeTools.getResultTerm(fsymTypeM).equals(TypeTools.getFunctionArgAt(fsymTypeM, j))) {
        return false;
    }
    // Functions with arity 1 are trivially 1-commutativ.
    if (arity == 1) {
        return true;
    }
    try {
        DefFunctionSymbol dsym = (DefFunctionSymbol)fsym;
        Boolean jc = dsym.isJCommutative(j);
        if (jc != null) {
            return jc.booleanValue();
        }
        if (arity == 2) {
        if (fsym instanceof DefFunctionSymbol) {
            if (this.isClass1Function(dsym) || this.isClass2Function(dsym)) {
            dsym.setJCommutativity(0,Boolean.valueOf(true));
            dsym.setJCommutativity(1,Boolean.valueOf(true));
            dsym.setTermination(true);
            this.obl.setTerminating(dsym);
            return true;
            }
        }
        }
        dsym.setJCommutativity(j, Boolean.valueOf(false));
    }
    catch (ClassCastException e) { }
    return false;
    }

    protected boolean isClass1Function(DefFunctionSymbol fsym) {
    // Check whether the fsym rules have the appropriate form.
    if (fsym.getArity() != 2) {
        return false;
    }
    Vector<Rule> rules = new Vector<Rule>();
    Vector<AlgebraTerm> conditions = new Vector<AlgebraTerm>();
    this.obl.liftRules((Set<Rule>)this.obl.defsrules.get(fsym), rules, conditions);
    if (rules.size() != 2) {
        return false;
    }
    Rule rule1 = null;
    Rule rule2 = null;
    AlgebraVariable y2 = null;
    AlgebraTerm cond1 = null;
    AlgebraTerm cond2 = null;
    Iterator it = rules.iterator();
    Iterator c_it = conditions.iterator();
    while (it.hasNext()) {
        Rule r = (Rule)it.next();
        AlgebraTerm c = (AlgebraTerm)c_it.next();
        if (r.getRight().isVariable()) {
        rule2 = r;
        cond2 = c;
        y2 = (AlgebraVariable)r.getRight();
        }
        else {
        cond1 = c;
        rule1 = r;
        }
    }
    if (rule1 == null || rule2 == null || rule1.getLeft().isVariable()) {
        return false;
    }
    int pos = -1;
    int i = 0;
    it = rule2.getLeft().getArguments().iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        if (t.equals(y2)) {
        pos = i;
        }
        i++;
    }
    if (pos < 0) {
        return false;
    }
    AlgebraTerm right1 = rule1.getRight();
    AlgebraTerm left1 = rule1.getLeft();
    SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)right1.getSymbol();
    if (gsym.getArity() != 1) {
        return false;
    }
    AlgebraTerm garg = right1.getArgument(0);
    AlgebraTerm gargTypeM = this.obl.typeContext.getSingleTypeOf(garg.getSymbol()).getTypeMatrix();

    AlgebraVariable x1 = (AlgebraVariable)left1.getArgument(1-pos);
    AlgebraTerm x1Type = TypeTools.getFunctionArgAt(this.obl.typeContext.getSingleTypeOf(left1.getSymbol()).getTypeMatrix(), 1-pos);

    AlgebraVariable y1 = (AlgebraVariable)left1.getArgument(pos);
    AlgebraTerm y1Type = TypeTools.getFunctionArgAt(this.obl.typeContext.getSingleTypeOf(left1.getSymbol()).getTypeMatrix(), pos);

    if (!fsym.equals(garg.getSymbol())) {
        //|| !(garg.getArgument(pos).equals(y1) || ) {
        return false;
    }
    AlgebraTerm r = null;
    AlgebraTerm rType = null;
    if (garg.getArgument(0).equals(y1)) {
        r = garg.getArgument(1);
        rType = TypeTools.getFunctionArgAt(gargTypeM,1);
    }
    else {
        if (!garg.getArgument(1).equals(y1)) {
        return false;
        }
        r = garg.getArgument(0);
        rType = TypeTools.getFunctionArgAt(gargTypeM,0);
    }
    // (a) Check that g is constructor-based.
    if (!this.isConstructorBased(gsym, 0)) {
        return false;
    }
    // (b) Check that y does not occur in r.
    if (r.getVars().contains(y1)) {
        return false;
    }
    // (c) Check that r[y/g(y)]==y
    AlgebraSubstitution sub = AlgebraSubstitution.create();
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    args.add(y1.deepcopy());
    sub.put((VariableSymbol)x1.getSymbol(), AlgebraFunctionApplication.create(gsym, args));
    RewriteCalculus rwc = RewriteCalculus.create(this.obl.rootprogram, this.obl.defsrules, this.obl.typeContext);
    if (!rwc.proveEquivalence(r.apply(sub), rType, y1.deepcopy(), y1Type)) {
        return false;
    }
    // (d1) Check that cond1 => g(r)==x
    args = new Vector<AlgebraTerm>();
    args.add(r);
    AlgebraTerm gr = AlgebraFunctionApplication.create(gsym, args);
    AlgebraTerm grType = TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(gsym).getTypeMatrix());
    if (!rwc.proveEquivalenceUnderCondition(gr, grType, x1.deepcopy(), x1Type, cond1)) {
        return false;
    }
    // (d2) Check that g(r)==x => cond1
    DefFunctionSymbol eq = this.obl.getEqualFunction(x1Type);
    args = new Vector<AlgebraTerm>();
    args.add(gr);
    args.add(x1.deepcopy());
    AlgebraTerm noteqterm = AlgebraFunctionApplication.create(eq, args);
    Vector<AlgebraTerm> notarg = new Vector<AlgebraTerm>();
    notarg.add(noteqterm);
    noteqterm = AlgebraFunctionApplication.create(this.obl.fNot, notarg);
    AlgebraTerm noteqType = TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(this.obl.fNot).getTypeMatrix());
    notarg = new Vector<AlgebraTerm>();
    notarg.add(cond1);
    AlgebraTerm notcond = AlgebraFunctionApplication.create(this.obl.fNot, notarg);
    if (!rwc.proveUnderCondition(noteqterm, noteqType, notcond)) {
        return false;
    }
    // (e) Check that !(cond1) && !cond1[x/y] => x==y
    args = new Vector<AlgebraTerm>();
    notarg = new Vector<AlgebraTerm>();
    notarg.add(cond1.deepcopy());
    args.add(AlgebraFunctionApplication.create(this.obl.fNot, notarg));
    sub = AlgebraSubstitution.create();
    sub.put((VariableSymbol)x1.getSymbol(), y1);
    notarg = new Vector<AlgebraTerm>();
    notarg.add(cond1.apply(sub));
    args.add(AlgebraFunctionApplication.create(this.obl.fNot, notarg));
    AlgebraTerm curcond = AlgebraFunctionApplication.create(this.obl.fAnd, args);
    args = new Vector<AlgebraTerm>();
    args.add(x1.deepcopy());
    args.add(y1.deepcopy());
    AlgebraTerm curterm = AlgebraFunctionApplication.create(eq, args);
    AlgebraTerm curtermType = TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(eq).getTypeMatrix());
    return rwc.proveUnderCondition(curterm, curtermType, curcond);
    }

    protected boolean isClass2Function(DefFunctionSymbol fsym) {
    if (fsym.getArity() != 2) {
        return false;
    }
    Vector<Rule> rules = new Vector<Rule>();
    Vector<AlgebraTerm> conditions = new Vector<AlgebraTerm>();
    this.obl.liftRules((Set<Rule>)this.obl.defsrules.get(fsym), rules, conditions);
    if (rules.size() != 2) {
        return false;
    }
    Rule rule1 = null;
    Rule rule2 = null;
    AlgebraTerm cond1 = null;
    AlgebraTerm cond2 = null;
    AlgebraTerm t = null;
    Iterator it = rules.iterator();
    Iterator c_it = conditions.iterator();
    while (it.hasNext()) {
        Rule r = (Rule)it.next();
        AlgebraTerm right = r.getRight();
        AlgebraTerm c = (AlgebraTerm)c_it.next();
        if (right.getDefFunctionSymbols().isEmpty() && right.getVars().isEmpty()) {
        rule2 = r;
        cond2 = c;
        t = right;
        }
        else {
        cond1 = c;
        rule1 = r;
        }
    }
    if (rule1 == null || rule2 == null || rule1.getRight().isVariable()) {
        return false;
    }
    AlgebraTerm left1 = rule1.getLeft();
    SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)rule1.getRight().getSymbol();
    if (gsym.getArity() != 2 || !(gsym instanceof DefFunctionSymbol)) {
        return false;
    }
    AlgebraVariable y1 = null;
    AlgebraTerm r = null;
    it = rule1.getRight().getArguments().iterator();
    while (it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        if (arg.isVariable()) {
        y1 = (AlgebraVariable)arg;
        }
        else {
        if (!arg.getSymbol().equals(fsym)) {
            return false;
        }
        r = arg;
        }
    }
    if (y1 == null) {
        return false;
    }
    if (r.getArgument(0).equals(y1)) {
        r = r.getArgument(1);
    }
    else {
        r = r.getArgument(0);
    }
    if (cond1.getVars().contains(y1) || r.getVars().contains(y1)) {
        return false;
    }
    AlgebraTerm x1 = left1.getArgument(0);
    if (x1.equals(y1)) {
        x1 = left1.getArgument(1);
    }
    AlgebraSubstitution sub = AlgebraSubstitution.create();
    sub.put((VariableSymbol)x1.getSymbol(), t);
    RewriteCalculus rwc = RewriteCalculus.create(this.obl.rootprogram, this.obl.defsrules, this.obl.typeContext);
    AlgebraTerm boolType = TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(this.obl.cFalse).getTypeMatrix());
    if (!rwc.proveUnderCondition(AlgebraFunctionApplication.create(this.obl.cFalse), boolType, cond1.apply(sub))) {
        return false;
    }
    if  (this.isClass1Function((DefFunctionSymbol)gsym)) {
        return true;
    }
    else {
        return false;
    }
    }

    protected boolean isConstructorBased(SyntacticFunctionSymbol fsym, int j) {
    if (fsym.getArity() <= j) {
        return false;
    }
    if (fsym instanceof ConstructorSymbol) {
        return true;
    }
    if (this.obl.isMutuallyRecursive((DefFunctionSymbol)fsym)) {
        return false;
    }
    Position epsilon = Position.create();
    Set<Rule> rules = this.obl.liftRules((Set<Rule>)this.obl.defsrules.get(fsym));
    Iterator it = rules.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraTerm right = rule.getRight();
        Iterator f_it  = right.getDefFunctionSymbols().iterator();
        while (f_it.hasNext()) {
        DefFunctionSymbol gsym = (DefFunctionSymbol)f_it.next();
        if (!gsym.getTermination()) {
            return false;
        }
        }
        AlgebraVariable y = (AlgebraVariable)rule.getLeft().getArgument(j);
        // Looking for a suitable pi.
        Iterator p_it = right.getPositions().iterator();
        while (p_it.hasNext()) {
        Position pi = (Position)p_it.next();
        AlgebraTerm t = right.getSubterm(pi);
        if (t.equals(y) && !pi.equals(epsilon)) {
            Iterator p2_it = pi.iterator();
            Position pi2 = Position.create();
            boolean allPositionsOk = true;
            while (p2_it.hasNext()) {
            int k = ((Integer)p2_it.next()).intValue();
            AlgebraTerm t2 = right.getSubterm(pi);
            if (!this.isConstructorBased((SyntacticFunctionSymbol)t2.getSymbol(), k)) {
                allPositionsOk = false;
                break;
            }
            pi2.add(k);
            }
            if (allPositionsOk) {
            // found a suitable position.
            return true;
            }
        }
        }
    }
    return false;
    }

    /**
     * orders a vector of DefFunctionSymbols according to the numbers they have in between "^" and "_"
     * a function that does not have a number is considered high (see MAXX in getFuncNum).
     */
    private Vector<DefFunctionSymbol> sortByDefFuncNum(Collection<DefFunctionSymbol> defs) {
        DefFunctionSymbol[] defsArr = defs.toArray(new DefFunctionSymbol[0]);
        this.sortByDefFuncNum(defsArr, 0, defsArr.length-1);
        return new Vector<DefFunctionSymbol>(Arrays.asList(defsArr));
    }

    /** quicksorts the array by numbers
     */
    private void sortByDefFuncNum(DefFunctionSymbol[] defsArr, int low, int high) {
        if(low>=high) {
            return;
        }
        int i=low, j=high-1;
        int pivot = this.getFuncNum(defsArr[high]);
        while(true) {
            while( (i<high) && (this.getFuncNum(defsArr[i])<pivot) ) {
                ++i;
            }
            while( (j>low) && (this.getFuncNum(defsArr[j])>=pivot) ) {
                --j;
            }
            if (i>=j) {
                break;
            }
            this.xchange(defsArr,i,j);
        }
        this.xchange(defsArr,i,high);
        this.sortByDefFuncNum(defsArr,low,i-1);
        this.sortByDefFuncNum(defsArr,i+1,high);
    }


    /** retrieves the number from a function symbol
     */
    private int getFuncNum(DefFunctionSymbol fsym) {
        final int MAXX = 200000;
        String name = fsym.getName();
        int idxHat = name.lastIndexOf('^');
        int idxBar = name.indexOf('_', idxHat);
        if ( (idxHat >= 0) && (idxBar > idxHat) ) {
            try {
                name = name.substring(idxHat+1, idxBar);
                return Integer.parseInt(name);
            }
            catch (Exception e) {
                return MAXX;
            }
        }
        return MAXX;
    }


    /** exchanges the elements arr[i] and arr[j]
     */
    private <T> void xchange (T[] arr, int i, int j) {
        T temp = arr[j];
        arr[j] = arr[i];
        arr[i] = temp;
    }

}
