package aprove.verification.theoremprover.Simplifier;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Verifier.*;

public abstract class BasicFixedValueSimplifier extends SimplifierProcessor {

    protected SimplifierObligation obl;
    protected Vector<Rule> fvtInfo;

    public BasicFixedValueSimplifier(String pName,String psName,String plName) {
        super(pName,psName,plName);
    }

    public boolean fixedValueTransformation(DefFunctionSymbol fsym) {
    return this.fixedValueTransformation(fsym, null) != null;
    }

    public void addfvtInfo(SyntacticFunctionSymbol fsym,Vector<AlgebraTerm> fixedvalues,Vector<AlgebraVariable> vars,SyntacticFunctionSymbol fnsym){
        Vector<AlgebraTerm> xs = new Vector<AlgebraTerm>();
        Vector<AlgebraTerm> ys = new Vector<AlgebraTerm>();
        Iterator w_it = fixedvalues.iterator();
        Iterator v_it = vars.iterator();
        while (w_it.hasNext()){
            AlgebraTerm w = (AlgebraTerm) w_it.next();
            AlgebraTerm v = (AlgebraTerm) v_it.next();
            if (w == null) {
                xs.add(v);
                ys.add(v);
            } else {
                xs.add(w);
            }
        }
        this.fvtInfo.add(Rule.create(AlgebraFunctionApplication.create(fsym,xs),AlgebraFunctionApplication.create(fnsym,ys)));
    }

    public void resetfvtInfo(){
        this.fvtInfo = new Vector<Rule>();
    }

    public Vector<Rule> getfvtInfo(){
        return this.fvtInfo;
    }

    /** Performes a fixed-value-transformation for a given defining function and changes
     *  as much rules as possible to use the new function.
     */
    public DefFunctionSymbol fixedValueTransformation(DefFunctionSymbol fsym, Hashtable origin) {
    Vector fsCritRecCalls = new Vector();
    Vector<Rule> rules = new Vector<Rule>();
    DefFunctionSymbol forigin = null;
    if (origin != null) {
        forigin = (DefFunctionSymbol)origin.get(fsym);
    }
    Vector<AlgebraVariable> zs = new Vector<AlgebraVariable>();

    // TODO removal of sorts
    if (aprove.Globals.useAssertions) {
        assert fsym.getArgSorts() != null : "argSorts() of "+fsym+" is null!";
    }
    Iterator it = fsym.getArgSorts().iterator();

    for (int i=0; i<fsym.getArity(); i++) {

        // TODO removal of sorts
        Sort s = (Sort)it.next();

        String name = this.obl.symbnames.getFreshName("z_"+(i+1), false);
        AlgebraVariable z = AlgebraVariable.create(VariableSymbol.create(name, s));
        zs.add(z);
    }
    Iterator<DefFunctionSymbol> it_def = (new Vector<DefFunctionSymbol>(this.obl.defsrules.keySet())).iterator();
    while (it_def.hasNext()) {
        DefFunctionSymbol gsym = it_def.next();
        if (this.obl.directlyDependsOn(gsym, fsym)) {
            rules.addAll(this.obl.defsrules.get(gsym));
        }
    }
    Set<Vector<AlgebraTerm>> fixedTerms = new HashSet<Vector<AlgebraTerm>>();
    Iterator r_it = rules.iterator();
    while (r_it.hasNext()) {
        Rule rule = (Rule)r_it.next();
        Vector<AlgebraTerm> fifo = new Vector<AlgebraTerm>();
        // Looking for fixed calls.
        fifo.add(rule.getRight());
        while (!fifo.isEmpty()) {
        AlgebraTerm term = fifo.remove(0);
        if (term.isVariable()) {
            continue;
        }
        SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)term.getSymbol();
        if (gsym.equals(fsym)) {
            Vector<AlgebraTerm> qs = this.getFixedTerms(fsym, term.getArguments(), zs);
            // Split the solution.
            BigInteger max = BigInteger.ZERO.setBit(fsym.getArity());
            for (BigInteger i=BigInteger.ONE; !i.equals(max); i=i.add(BigInteger.ONE)) {
            Vector<AlgebraTerm> nqs = new Vector<AlgebraTerm>();
            Iterator q_it = qs.iterator();
            for (int j=0; q_it.hasNext(); j++) {
                AlgebraTerm q = (AlgebraTerm)q_it.next();
                nqs.add(i.testBit(j) ? q : null);
            }
            fixedTerms.add(nqs);
            }
        }
        fifo.addAll(term.getArguments());
        }
    }
//    it = fixedTerms.iterator();
    Iterator<Vector<AlgebraTerm>> it_fixedTerms = fixedTerms.iterator();
    while (it_fixedTerms.hasNext()) {
        Vector<AlgebraTerm> qs = it_fixedTerms.next();
        boolean onlynull = true;
        Iterator q_it = qs.iterator();
        while (onlynull && q_it.hasNext()) {
        AlgebraTerm q = (AlgebraTerm)q_it.next();
        if (q != null) {
            onlynull = false;
        }
        }
        if (!onlynull) {
        // Application of the fixed-value rule is sugested.
        // Now check whether it is possible.
        if (this.recFixedValIsEqual(fsym, qs, zs)) {
            if (this.fixedTermIsEvaluated(fsym, qs, zs, origin)) {
                        DefFunctionSymbol fnsym = this.fixedValueTransformation(fsym, qs, zs);
                        this.addfvtInfo(fsym,qs,zs,fnsym);
                        return fnsym;
            }
        }
        else if (this.obl.critRecCallsTable != null) {
            // Application is blocked by the form of the
            // recursive calls. Maybe recursion-shift
            // can fix this.
            Object tmp[] = new Object[3];
            tmp[0] = this.getProblematicRecursiveCalls(fsym, qs, zs);
            tmp[1] = qs;
            tmp[2] = zs;
            fsCritRecCalls.add(tmp);
        }
        }
    }
    if (this.obl.critRecCallsTable != null) {
        this.obl.critRecCallsTable.put(fsym, fsCritRecCalls);
    }
    return null;
    }

    /** Checks whether there is a term which calls f (given by fsym)
     *  with the fixed values given in qs.
     */
    protected boolean fixedTermIsEvaluated(DefFunctionSymbol fsym, Vector<AlgebraTerm> qs, Vector<AlgebraVariable> zs, Hashtable origin) {
    Vector<Rule> rules = new Vector<Rule>();
    Vector<AlgebraTerm> conditions = new Vector<AlgebraTerm>();
    DefFunctionSymbol forigin = fsym;
    if (origin != null) {
        forigin = (DefFunctionSymbol)origin.get(fsym);
        if (forigin == null) {
        forigin = fsym;
        }
    }
    Iterator<DefFunctionSymbol> it_defs = (new Vector<DefFunctionSymbol>(this.obl.defs)).iterator();
    while (it_defs.hasNext()) {
        DefFunctionSymbol gsym = it_defs.next();
        DefFunctionSymbol gorigin = gsym;
        if (origin != null) {
        gorigin = (DefFunctionSymbol)origin.get(gsym);
        if (gorigin == null) {
            gorigin = gsym;
        }
        }
        if (this.obl.greater_dep(gorigin, forigin)) {
        this.obl.liftRules((Set<Rule>)this.obl.defsrules.get(gsym), rules, conditions);
        }
    }
    RewriteCalculus rwc = RewriteCalculus.create(this.obl.rootprogram, this.obl.defsrules, this.obl.typeContext);
    Iterator r_it = rules.iterator();
    Iterator c_it = conditions.iterator();
    while (r_it.hasNext()) {
        Rule rule = (Rule)r_it.next();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm condition = (AlgebraTerm)c_it.next();
        if (this.fixedTermIsEvaluated(fsym, rule.getRight(), condition, qs, zs, rwc)) {
        return true;
        }
    }
    return false;
    }

    protected boolean fixedTermIsEvaluated(DefFunctionSymbol fsym, AlgebraTerm term, AlgebraTerm condition, Vector<AlgebraTerm> qs, Vector<AlgebraVariable> zs, RewriteCalculus rwc) {
        if (!term.isVariable()) {
            SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)term.getSymbol();
            if (gsym.equals(fsym)) {
                AlgebraSubstitution sigma = AlgebraSubstitution.create();
                Iterator z_it = zs.iterator();
                Iterator a_it = term.getArguments().iterator();
                while (z_it.hasNext()) {
                    AlgebraVariable z = (AlgebraVariable)z_it.next();
                    AlgebraTerm arg = (AlgebraTerm)a_it.next();
                    sigma.put((VariableSymbol)z.getSymbol(), arg);
                }
                boolean all_equal = true;
                Iterator q_it = qs.iterator();
                a_it = term.getArguments().iterator();
                AlgebraTerm gsymTypeM = this.obl.typeContext.getSingleTypeOf(gsym).getTypeMatrix();
                Iterator<AlgebraTerm> aType_it = TypeTools.getFunctionArgs(gsymTypeM).iterator();
                while (q_it.hasNext()) {
                    AlgebraTerm q = (AlgebraTerm)q_it.next();
                    AlgebraTerm arg = (AlgebraTerm)a_it.next();
                    AlgebraTerm argType = aType_it.next();
                    if (q != null) {
                        q = q.apply(sigma);
                        // assuming that arg and q have the same type, otherwise we should not be here
                        if (!rwc.proveEquivalenceUnderCondition(arg, argType, q, argType, condition)) {
                            all_equal = false;
                            break;
                        }
                    }
                }
                if (all_equal) {
                    return true;
                }
            }
            Iterator it = term.getArguments().iterator();
            while (it.hasNext()) {
                AlgebraTerm t = (AlgebraTerm)it.next();
                if (this.fixedTermIsEvaluated(fsym, t, condition, qs, zs, rwc)) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Checks whether the recursive calls of fsym are equal to their
     *  fixed call.
     */
    protected boolean recFixedValIsEqual(DefFunctionSymbol fsym, Vector<AlgebraTerm> qs, Vector<AlgebraVariable> zs) {
    Vector<Rule> rules = new Vector<Rule>();
    Vector<AlgebraTerm> conditions = new Vector<AlgebraTerm>();
    this.obl.liftRules((Set<Rule>)this.obl.defsrules.get(fsym), rules, conditions);
    RewriteCalculus rwc = RewriteCalculus.create(this.obl.rootprogram, this.obl.defsrules, this.obl.typeContext);
    Iterator r_it = rules.iterator();
    Iterator c_it = conditions.iterator();
    while (r_it.hasNext()) {
        Rule rule = (Rule)r_it.next();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm condition = (AlgebraTerm)c_it.next();
        AlgebraSubstitution sigma1 = AlgebraSubstitution.create();
        Vector<AlgebraVariable> zs2 = new Vector<AlgebraVariable>();
        Iterator z_it = zs.iterator();
        Iterator a_it = left.getArguments().iterator();
        while (z_it.hasNext()) {
        AlgebraVariable z = (AlgebraVariable)z_it.next();
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        sigma1.put((VariableSymbol)z.getSymbol(), arg);
        zs2.add((AlgebraVariable) arg);
        }
        Vector<AlgebraTerm> qs2 = new Vector<AlgebraTerm>();
        AlgebraSubstitution sigma2 = AlgebraSubstitution.create();
        Iterator q_it = qs.iterator();
        for (int i=0; q_it.hasNext(); i++) {
        AlgebraTerm q = (AlgebraTerm)q_it.next();
        if (q != null) {
            AlgebraTerm q2 = q.apply(sigma1);
            sigma2.put((VariableSymbol)left.getArgument(i).getSymbol(), q2);
            qs2.add(q2);
        }
        else {
            qs2.add(null);
        }
        }
        if (!this.recFixedValIsEqual(fsym, rule.getRight(), condition.apply(sigma2), qs2, zs2, sigma2, rwc)) {
        return false;
        }
    }
    return true;
    }

    protected boolean recFixedValIsEqual(DefFunctionSymbol fsym, AlgebraTerm term, AlgebraTerm condition, Vector<AlgebraTerm> qs, Vector<AlgebraVariable> zs, AlgebraSubstitution sigma, RewriteCalculus rwc) {
    if (!term.isVariable()) {
        SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)term.getSymbol();
        if (gsym.equals(fsym)) {
        AlgebraSubstitution sigma2 = AlgebraSubstitution.create();
        Iterator q_it = qs.iterator();
        Iterator z_it = zs.iterator();
        Iterator a_it = term.getArguments().iterator();
        while (q_it.hasNext()) {
            AlgebraTerm q = (AlgebraTerm)q_it.next();
            AlgebraVariable z = (AlgebraVariable)z_it.next();
            AlgebraTerm arg = (AlgebraTerm)a_it.next();
            if (q == null) {
            sigma2.put((VariableSymbol)z.getSymbol(), arg);
            }
        }
        q_it = qs.iterator();
        a_it = term.getArguments().iterator();
        AlgebraTerm gsymTypeM = this.obl.typeContext.getSingleTypeOf(gsym).getTypeMatrix();
        Iterator<AlgebraTerm> aType_it = TypeTools.getFunctionArgs(gsymTypeM).iterator();
        while (q_it.hasNext()) {
            AlgebraTerm q = (AlgebraTerm)q_it.next();
            AlgebraTerm arg = (AlgebraTerm)a_it.next();
            AlgebraTerm argType = aType_it.next();
            arg = arg.apply(sigma);
            if (q != null) {
            q = q.apply(sigma2).apply(sigma);
            // assuming that arg and q have the same type
            if (!rwc.proveEquivalenceUnderCondition(arg, argType, q, argType, condition)) {
                return false;
            }
            }
        }
        }
        Iterator it = term.getArguments().iterator();
        while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        if (!this.recFixedValIsEqual(fsym, t, condition, qs, zs, sigma, rwc)) {
            return false;
        }
        }
    }
    return true;
    }

    protected Vector<AlgebraTerm> getFixedTerms(DefFunctionSymbol fsym, List<AlgebraTerm> terms, List<AlgebraVariable> zs) {
    BigInteger fixed = BigInteger.ZERO;
    BigInteger needed = BigInteger.ZERO;
    Vector<AlgebraTerm> qs = new Vector<AlgebraTerm>();
    Hashtable<AlgebraVariable, Integer> zsindex = new Hashtable<AlgebraVariable, Integer>();
    qs.setSize(terms.size());
    Iterator<AlgebraTerm> it = terms.iterator();
    Iterator<AlgebraVariable> z_it = zs.iterator();
    for (int i=0; it.hasNext(); i++) {
        AlgebraTerm t = it.next();
        AlgebraVariable z = z_it.next();
        if (t.getVars().isEmpty()) {
        qs.set(i, t);
        fixed = fixed.setBit(i);
        }
        zsindex.put(z, i);
    }
    TreeSet<IndexedTerm> sorted = new TreeSet<IndexedTerm>();
    int i = 0;
    for (AlgebraTerm t : terms) {
        sorted.add(new IndexedTerm(t, i++));
    }
    for (IndexedTerm ti : sorted) {
        AlgebraTerm t = ti.getTerm();
        i = ti.getIndex();
        if (fixed.testBit(i) || needed.testBit(i)) {
        continue;
        }
        Hashtable replacements = new Hashtable();
        Iterator<AlgebraTerm> t_it = terms.iterator();
        z_it = zs.iterator();
        for (int j=0; t_it.hasNext(); j++) {
        AlgebraTerm t1 = t_it.next();
        AlgebraVariable z = z_it.next();
        if (i!=j && !fixed.testBit(j)) {
            replacements.put(t1,z);
        }
        }
        AlgebraTerm tr = t.termReplace(replacements);
        Set<AlgebraVariable> vars = tr.getVars();
        if (zs.containsAll(vars)) {
        qs.set(i, tr);
        Iterator<AlgebraVariable> v_it = vars.iterator();
        while (v_it.hasNext()) {
            AlgebraVariable z = v_it.next();
            int j = zsindex.get(z).intValue();
            needed = needed.setBit(j);
        }
        }
    }
    return qs;
    }

    /** Performs a fixed value transformation of fsym with q.
     */
    public DefFunctionSymbol fixedValueTransformation(DefFunctionSymbol fsym, Vector<AlgebraTerm> qs, Vector<AlgebraVariable> zs) {
    String name = this.obl.symbnames.getFreshName(fsym.getName(), false);

    // TODO removal of sorts
    Vector<Sort> sorts = new Vector<Sort>();
    Iterator<Sort> s_it = fsym.getArgSorts().iterator();

    BigInteger fixed = BigInteger.ZERO;

    AlgebraTerm fsymTypeM = this.obl.typeContext.getSingleTypeOf(fsym).getTypeMatrix();
    Vector<AlgebraTerm> argTypes = new Vector<AlgebraTerm>();
    Iterator<AlgebraTerm> it_argTypes = TypeTools.getFunctionArgs(fsymTypeM).iterator();

    Iterator q_it = qs.iterator();
    for (int i=0; it_argTypes.hasNext(); i++) {

        // TODO removal of sorts
        Sort s = s_it.next();

        AlgebraTerm argType = it_argTypes.next();

        AlgebraTerm q = (AlgebraTerm)q_it.next();
        if (q == null) {

            // TODO removal of sorts
            sorts.add(s);

            argTypes.add(argType);
        }
        else {
        fixed = fixed.setBit(i);
        }
    }
    DefFunctionSymbol fnsym = DefFunctionSymbol.create(name, sorts, fsym.getSort());

    this.obl.typeContext.setSingleTypeOf(fnsym, new Type(TypeTools.function(argTypes,TypeTools.getResultTerm(fsymTypeM))));

    Set<Rule> newrules = new HashSet<Rule>();
    Iterator it = this.obl.moveMatchingToCondition((Set<Rule>)this.obl.defsrules.get(fsym)).iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm right = rule.getRight();

        Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();

        Vector<AlgebraTerm> qs2 = new Vector<AlgebraTerm>();
        Vector<AlgebraTerm> qs2Types = new Vector<AlgebraTerm>();

        AlgebraSubstitution sigma1 = AlgebraSubstitution.create();
        AlgebraTerm leftTypeM = this.obl.typeContext.getSingleTypeOf(left.getSymbol()).getTypeMatrix();
        Iterator a_it = left.getArguments().iterator();
        Iterator z_it = zs.iterator();
        while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        AlgebraVariable z = (AlgebraVariable)z_it.next();
        sigma1.put((VariableSymbol)z.getSymbol(), arg);
        }
        AlgebraSubstitution sigma2 = AlgebraSubstitution.create();
        a_it = left.getArguments().iterator();
        q_it = qs.iterator();
        Iterator<AlgebraTerm> argType_it = TypeTools.getFunctionArgs(leftTypeM).iterator();
        for (int i=0; a_it.hasNext(); i++) {
        AlgebraTerm argType = argType_it.next();
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        AlgebraTerm q = (AlgebraTerm)q_it.next();
        if (q != null) {
            AlgebraTerm q1 = q.apply(sigma1);
            sigma2.put((VariableSymbol)arg.getSymbol(), q1);
            qs2.add(q1.deepcopy());

//            qs2Types.add(TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(q1.getSymbol()).getTypeMatrix()));
            qs2Types.add(argType);
        }
        else {
            newargs.add(arg);
        }
        }
        Vector<Rule> newconds = new Vector<Rule>();
        Iterator cond_it = rule.getConds().iterator();
        while (cond_it.hasNext()) {
        Rule cond = (Rule)cond_it.next();
        newconds.add(Rule.create(cond.getLeft().apply(sigma2), cond.getRight()));
        }
        AlgebraTerm newleft = AlgebraFunctionApplication.create(fnsym, newargs);
        AlgebraTerm newright = right.apply(sigma2);
        if (newconds.isEmpty()) {
            newright = this.obl.makeProjectionTyped(newright, TypeTools.getResultTerm(fsymTypeM), qs2, qs2Types);
        }
        else {
        Rule cond = newconds.remove(0);

        AlgebraTerm condLeftType = SimplifierTools.getTypeOfTerm(cond.getLeft(), rule, this.obl.typeContext);

        if(aprove.Globals.useAssertions) {
            assert condLeftType != null : "no type was found for "+cond.getLeft();
        }

        AlgebraTerm condLeft = this.obl.makeProjectionTyped(cond.getLeft(), condLeftType, qs2, qs2Types);

        cond = Rule.create(condLeft, cond.getRight());
        newconds.insertElementAt(cond, 0);
        }
        newrules.add(Rule.create(newconds, newleft, newright));
    }
    this.obl.defs.add(fnsym);
    this.obl.defsrules.put(fnsym, newrules);
    this.obl.updateSymbol(fnsym, newrules);
    this.obl.symbolicEvaluation(fnsym);
    // Use the new function.
    RewriteCalculus rwc = RewriteCalculus.create(this.obl.rootprogram, this.obl.defsrules, this.obl.typeContext);
    it = (new Vector(this.obl.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol gsym = (DefFunctionSymbol)it.next();
        newrules = new HashSet<Rule>();
        Iterator r_it = ((Set)this.obl.defsrules.get(gsym)).iterator();
        while (r_it.hasNext()) {
        Rule rule = (Rule)r_it.next();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm curcond = AlgebraFunctionApplication.create(this.obl.cTrue);
        Vector<Rule> newconds = new Vector<Rule>();
        Iterator c_it = rule.getConds().iterator();
        while (c_it.hasNext()) {
            Rule cond = (Rule)c_it.next();
            AlgebraTerm cleft = this.resolveFixedRuleTerm(fsym, fnsym, qs, zs, cond.getLeft(), curcond, rwc);
            AlgebraTerm cright = cond.getRight();
            Vector<AlgebraTerm> condterms = new Vector<AlgebraTerm>();
            this.obl.getLiftConditions(cright, cleft, condterms);
            Iterator ct_it = condterms.iterator();
            while (ct_it.hasNext()) {
            Vector<AlgebraTerm> andargs = new Vector<AlgebraTerm>();
            andargs.add(curcond);
            andargs.add((AlgebraTerm) ct_it.next());
            curcond = AlgebraFunctionApplication.create(this.obl.fAnd, andargs);
            }
            newconds.add(Rule.create(cleft, cright));
        }
        AlgebraTerm right = this.resolveFixedRuleTerm(fsym, fnsym, qs, zs, rule.getRight(), curcond, rwc);
        newrules.add(Rule.create(rule.getConds(), left, right));
        }
        this.obl.defsrules.put(gsym, newrules);
        this.obl.updateSymbol(gsym, newrules);
    }
    return fnsym;
    }

    /** Transforms a given term to use fnsym instead of fsym.
     */
    protected AlgebraTerm resolveFixedRuleTerm(DefFunctionSymbol fsym, DefFunctionSymbol fnsym, Vector<AlgebraTerm> qs, Vector<AlgebraVariable> zs, AlgebraTerm term, AlgebraTerm cond, RewriteCalculus rwc) {
    if (term.isVariable()) {
        return term;
    }
    SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)term.getSymbol();
    if (gsym.equals(fsym)) {
        AlgebraSubstitution sigma = AlgebraSubstitution.create();
        Iterator z_it = zs.iterator();
        Iterator a_it = term.getArguments().iterator();
        while (z_it.hasNext()) {
        AlgebraVariable z = (AlgebraVariable)z_it.next();
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        sigma.put((VariableSymbol)z.getSymbol(), arg);
        }
        boolean all_qs_equal = true;
        Iterator q_it = qs.iterator();
        a_it = term.getArguments().iterator();
        AlgebraTerm gsymTypeM = this.obl.typeContext.getSingleTypeOf(gsym).getTypeMatrix();
        Iterator<AlgebraTerm> aType_it = TypeTools.getFunctionArgs(gsymTypeM).iterator();
        while (q_it.hasNext()) {
        AlgebraTerm q = (AlgebraTerm)q_it.next();
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        AlgebraTerm argType = aType_it.next();
        if (q != null) {
            // assuming that arg and q have the same type
            if (!rwc.proveEquivalenceUnderCondition(arg, argType, q.apply(sigma), argType, cond)) {
            all_qs_equal = false;
            break;
            }
        }
        }
        if (all_qs_equal) {
        Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
        a_it = term.getArguments().iterator();
        q_it = qs.iterator();
        while (a_it.hasNext()) {
            AlgebraTerm arg = (AlgebraTerm)a_it.next();
            AlgebraTerm q = (AlgebraTerm)q_it.next();
            if (q == null) {
            newargs.add(this.resolveFixedRuleTerm(fsym, fnsym, qs, zs, arg, cond, rwc));
            }
        }
        return AlgebraFunctionApplication.create(fnsym, newargs);
        }
    }
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    Iterator a_it = term.getArguments().iterator();
    while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        newargs.add(this.resolveFixedRuleTerm(fsym, fnsym, qs, zs, arg, cond, rwc));
    }
    return AlgebraFunctionApplication.create(gsym, newargs);
    }

    protected class IndexedTerm implements Comparable {

    protected AlgebraTerm term;
    protected int index;

    public IndexedTerm(AlgebraTerm t, int i) {
        this.term = t;
        this.index = i;
    }

    @Override
    public int compareTo(Object o) {
        if (o instanceof IndexedTerm) {
        IndexedTerm that = (IndexedTerm)o;
        if (this.term.isSubtermOf(that.getTerm())) {
            return -1;
        }
        if (that.getTerm().isSubtermOf(this.term)) {
            return 1;
        }
        }
        return 0;
    }

    public AlgebraTerm getTerm() {
        return this.term;
    }

    public int getIndex() {
        return this.index;
    }
    }

    /** Returns a vector of problematic recursive calls.
     */
    protected Vector getProblematicRecursiveCalls(DefFunctionSymbol fsym, Vector<AlgebraTerm> qs, Vector<AlgebraVariable> zs) {
    Vector critRecCalls = new Vector();
    Set<Rule> rules = (Set<Rule>)this.obl.defsrules.get(fsym);
    AlgebraTerm gleft = null;
    RewriteCalculus rwc = RewriteCalculus.create(this.obl.rootprogram, this.obl.defsrules, this.obl.typeContext);
    Iterator r_it = rules.iterator();
    while (r_it.hasNext()) {
        Rule rule = (Rule)r_it.next();
        Object o[] = this.obl.getLiftedRuleWithCondition(rule);
        Rule lrule = (Rule)o[0];
        AlgebraTerm condition = (AlgebraTerm)o[1];
        AlgebraTerm lright = lrule.getRight();
        // Make sure every rule has the same lhs.
        if (gleft == null) {
        gleft = lrule.getLeft();
        }
        else {
        try {
            AlgebraSubstitution sub = gleft.matches(lrule.getLeft());
            lright = lright.apply(sub);
            condition = condition.apply(sub);
        }
        catch (UnificationException e) { }
        }
        AlgebraSubstitution sigma1 = AlgebraSubstitution.create();
        Vector<AlgebraVariable> zs2 = new Vector<AlgebraVariable>();
        Iterator z_it = zs.iterator();
        Iterator a_it = gleft.getArguments().iterator();
        while (z_it.hasNext()) {
        AlgebraVariable z = (AlgebraVariable)z_it.next();
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        sigma1.put((VariableSymbol)z.getSymbol(), arg);
        zs2.add((AlgebraVariable) arg);
        }
        Vector<AlgebraTerm> qs2 = new Vector<AlgebraTerm>();
        AlgebraSubstitution sigma2 = AlgebraSubstitution.create();
        Iterator q_it = qs.iterator();
        for (int i=0; q_it.hasNext(); i++) {
        AlgebraTerm q = (AlgebraTerm)q_it.next();
        if (q != null) {
            AlgebraTerm q2 = q.apply(sigma1);
            sigma2.put((VariableSymbol)gleft.getArgument(i).getSymbol(), q2);
            qs2.add(q2);
        }
        else {
            qs2.add(null);
        }
        }
        Hashtable rwpairs = new Hashtable();
        this.getProblematicRecursiveCalls(fsym, lrule.getRight(), condition.apply(sigma2), qs2, zs2, sigma2, rwpairs, Position.create(), rwc);
        o = new Object[4];
        o[0] = rule;
        o[1] = lrule;
        o[2] = condition;
        o[3] = rwpairs;
        critRecCalls.add(o);
    }
    return critRecCalls;
    }

    protected void getProblematicRecursiveCalls(DefFunctionSymbol fsym, AlgebraTerm term, AlgebraTerm condition, Vector<AlgebraTerm> qs, Vector<AlgebraVariable> zs, AlgebraSubstitution sigma, Hashtable rwpairs, Position pi, RewriteCalculus rwc) {
    if (!term.isVariable()) {
        SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)term.getSymbol();
        if (gsym.equals(fsym)) {
        AlgebraSubstitution sigma2 = AlgebraSubstitution.create();
        Iterator q_it = qs.iterator();
        Iterator z_it = zs.iterator();
        Iterator a_it = term.getArguments().iterator();
        while (q_it.hasNext()) {
            AlgebraTerm q = (AlgebraTerm)q_it.next();
            AlgebraVariable z = (AlgebraVariable)z_it.next();
            AlgebraTerm arg = (AlgebraTerm)a_it.next();
            if (q == null) {
            sigma2.put((VariableSymbol)z.getSymbol(), arg);
            }
        }
        q_it = qs.iterator();
        a_it = term.getArguments().iterator();
        AlgebraTerm gsymTypeM = this.obl.typeContext.getSingleTypeOf(gsym).getTypeMatrix();
        Iterator<AlgebraTerm> aType_it = TypeTools.getFunctionArgs(gsymTypeM).iterator();
        while (q_it.hasNext()) {
            AlgebraTerm q = (AlgebraTerm)q_it.next();
            AlgebraTerm arg = (AlgebraTerm)a_it.next();
            AlgebraTerm argType = aType_it.next();
            arg = arg.apply(sigma);
            if (q != null) {
            q = q.apply(sigma2).apply(sigma);
            // assuming that arg and q have the same type
            if (!rwc.proveEquivalenceUnderCondition(arg, argType, q, argType, condition)) {
                rwpairs.put(pi, term.getArguments());
            }
            }
        }
        }
        int i = 0;
        Iterator it = term.getArguments().iterator();
        while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        Position pi1 = pi.shallowcopy();
        pi1.add(i++);
        this.getProblematicRecursiveCalls(fsym, t, condition, qs, zs, sigma, rwpairs, pi1, rwc);
        }
    }
    }
}
