package aprove.verification.oldframework.Unification.Problems;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Unification.Utility.*;
import aprove.verification.oldframework.Utility.*;

/**
 *  Representation of a general AC-unification problem.
 *  <p>
 *  A. Boudet: "Competing for the AC-Unification Race", JAR 11, pp. 185-212
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class GeneralACProblem {

    private Set<AlgebraVariable> freeVars;
    private Set<AlgebraVariable> absVars;       // abstraction variables
    private Stack<PairOfACTerms> todo;
    private Map value;                    // value field for variables
    private Map counter;                  // counter for occur check
    private Map acProblems;               // problems for each ac symbol
    private Set<SyntacticFunctionSymbol> acSig;   // the ac symbols
    private boolean Fail;                 // did we fail?
    private FreshVarGenerator fvg;


    private GeneralACProblem(Set<SyntacticFunctionSymbol> acSig, Set<AlgebraVariable> freeVars, Set<AlgebraVariable> W) {
    this.acSig = acSig;
    this.freeVars = freeVars;
    this.absVars = new HashSet<AlgebraVariable>();
    this.todo = new Stack<PairOfACTerms>();
    this.value = new LinkedHashMap();
    this.counter = new LinkedHashMap();
    this.acProblems = new LinkedHashMap();

    Iterator i = acSig.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)i.next();
        this.acProblems.put(fun, new Vector<PairOfACTerms>());
    }

    this.Fail = false;
    this.fvg = new FreshVarGenerator(W, FreshNameGenerator.TYPE_INFERENCE);
    }

    private GeneralACProblem() {
    super();
    }

    public GeneralACProblem shallowcopy() {
    GeneralACProblem res = new GeneralACProblem();
    res.acSig = this.acSig;
    res.freeVars = this.freeVars;
    res.absVars = new HashSet<AlgebraVariable>(this.absVars);
    res.todo = new Stack<PairOfACTerms>();
    res.value = new LinkedHashMap(this.value);
    res.counter = new LinkedHashMap(this.counter);
    res.acProblems = new LinkedHashMap();
    Iterator i = this.acSig.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)i.next();
        res.acProblems.put(fun, new Vector<PairOfACTerms>((List<PairOfACTerms>)this.acProblems.get(fun)));
    }
    res.Fail = this.Fail;
    res.fvg = this.fvg.shallowcopy();

    return res;
    }


    /** Creates a new GeneralACProblem where acSig specifies the function
     * symbols that are AC and freeVars are the free variables occuring in the problem.
     */
    public static GeneralACProblem create(Set<SyntacticFunctionSymbol> acSig, Set<AlgebraVariable> freeVars, Set<AlgebraVariable> W) {
    return new GeneralACProblem(acSig, freeVars, W);
    }


    /** Returns the variables that were used for variable abstraction.
     */
    public Set<AlgebraVariable> getAbsVars() {
    return this.absVars;
    }

    /** Returns the fresh variable generator used by this problem.
     */
    public FreshVarGenerator getFreshVarGen() {
    return this.fvg;
    }


    /** Add an equation generated from s and t to the problem.
     */
    public void add(AlgebraTerm s, AlgebraTerm t) {
    this.add(PairOfACTerms.create(ACTerm.create(s, this.acSig), ACTerm.create(t, this.acSig)));
    }


    /** Adds a set of equations to the problem.
     */
    public void addAll(Collection<PairOfACTerms> coll) {
    Iterator i = coll.iterator();
    while(i.hasNext()) {
        PairOfACTerms next = (PairOfACTerms)i.next();
        this.add(next);
    }
    }


    /** Add an equation (i.e. a PairOfACTerms) to the problem.
     */
    public void add(PairOfACTerms pair) {

    this.todo.push(pair);

    while(!this.todo.isEmpty() && !this.Fail) {
        PairOfACTerms p = (PairOfACTerms)this.todo.pop();
        ACTerm l = p.getLeft();
        ACTerm r = p.getRight();
        Symbol lSymb = l.getSymbol();
        Symbol rSymb = r.getSymbol();

        if(lSymb.equals(rSymb)) {
        if(lSymb instanceof SyntacticFunctionSymbol) {
            SyntacticFunctionSymbol lFunSymb = (SyntacticFunctionSymbol)lSymb;
            if(!this.acSig.contains(lFunSymb)) {
            /* decomposition for free theory */
            Enumeration i = l.elements();
            Enumeration j = r.elements();
            while(i.hasMoreElements()) {
                this.todo.push(PairOfACTerms.create((ACTerm)i.nextElement(), (ACTerm)j.nextElement()));
            }
            }
            else {
            /* apply variable abstraction */
            VarAbstraction va = VarAbstraction.create(l, this.fvg);
            va.extend(r, this.fvg);
            this.absVars.addAll(va.getRange());
            ACTerm newL = l.apply(va);
            ACTerm newR = r.apply(va);
            ((List<PairOfACTerms>)this.acProblems.get(lSymb)).add(PairOfACTerms.create(newL, newR));
            Iterator i = va.getRange().iterator();
            while(i.hasNext()) {
                AlgebraVariable v = (AlgebraVariable)i.next();
                this.todo.add(PairOfACTerms.create(ACTerm.create(v, this.acSig), va.invGet(v)));
            }
            }
        }
        /* otherwise, they are equal variables and there's nothing to be done */
        }
        else {
        /* not equal */
        if((lSymb instanceof SyntacticFunctionSymbol) && (rSymb instanceof SyntacticFunctionSymbol)) {
            /* Conflict 1, i.e. Clash */
            this.Fail = true;
        }
        else {
            if(!(lSymb instanceof VariableSymbol)) {
                /* swap */
            ACTerm tmp1 = l;
            l = r;
            r = tmp1;
            Symbol tmp2 = lSymb;
            lSymb = rSymb;
            rSymb = tmp2;
            }
            /* lSymb is a variable symbol now */
            if(rSymb instanceof SyntacticFunctionSymbol) {
            SyntacticFunctionSymbol rFunSymb = (SyntacticFunctionSymbol)rSymb;
            if(this.acSig.contains(rFunSymb)) {
                /* apply variable abstraction */
                VarAbstraction va = VarAbstraction.create(r, this.fvg);
                this.absVars.addAll(va.getRange());
                ACTerm r1 = r.apply(va);
                Iterator i = va.getRange().iterator();
                while(i.hasNext()) {
                    AlgebraVariable v = (AlgebraVariable)i.next();
                    this.todo.add(PairOfACTerms.create(ACTerm.create(v, this.acSig), va.invGet(v)));
                }
                Object o = this.value.get(l);
                if(o==null) {
                this.setValue(l, r1);
                }
                else {
                ACTerm val = (ACTerm)o;
                if(val.getSymbol() instanceof SyntacticFunctionSymbol) {
                    if(!val.getSymbol().equals(rSymb)) {
                        /* Conflict 2 */
                        this.Fail = true;
                    }
                    else {
                        this.todo.add(PairOfACTerms.create(r, val));
                    }
                }
                else {
                    /* val is a variable */
                    if(!val.equals(l)) {
                    /* different variable */
                            this.todo.add(PairOfACTerms.create(val, r1));
                    }
                }
                }
            }
            else {
                /* free symbol */
                /* apply variable abstraction */
                VarAbstraction va = VarAbstraction.create(r, this.fvg);
                this.absVars.addAll(va.getRange());
                ACTerm r1 = r.apply(va);
                Iterator i = va.getRange().iterator();
                while(i.hasNext()) {
                    AlgebraVariable v = (AlgebraVariable)i.next();
                    this.todo.add(PairOfACTerms.create(ACTerm.create(v, this.acSig), va.invGet(v)));
                }
                Object o = this.value.get(l);
                if(o==null) {
                this.setValue(l, r1);
                }
                else {
                ACTerm val = (ACTerm)o;
                if(val.getSymbol() instanceof SyntacticFunctionSymbol) {
                    if(!val.getSymbol().equals(rSymb)) {
                        /* Conflict 2 */
                        this.Fail = true;
                    }
                    else {
                    if(val.length() < r.length()) {
                        ACTerm tmp = val;
                        val = r;
                        r = tmp;
                    }
                    /* |r| <= |val| */
                        this.todo.add(PairOfACTerms.create(r, val));
                    }
                }
                else {
                    /* val is a variable */
                    if(!val.equals(l)) {
                    /* different variable */
                            this.todo.add(PairOfACTerms.create(val, r1));
                    }
                }
                }
            }
            }
            else {
            /* r is a variable */
            ACTerm lRep = this.getRep(l);
            ACTerm rRep = this.getRep(r);

            /* there's nothing to be done if they have the same representative */
            if(!lRep.equals(rRep)) {
                Object vl = this.value.get(lRep);
                Object vr = this.value.get(rRep);
                if(vl==null) {
                this.setValue(lRep, rRep);
                }
                else if(vr==null) {
                this.setValue(rRep, lRep);
                }
                else {
                ACTerm lVal = (ACTerm)vl;
                ACTerm rVal = (ACTerm)vr;
                Symbol lvs = lVal.getSymbol();
                Symbol rvs = rVal.getSymbol();
                if(!lvs.equals(rvs)) {
                    /* Conflict 2, i.e. Clash */
                    this.Fail = true;
                }
                else {
                    /* equal function symbols */
                    SyntacticFunctionSymbol lValSymb = (SyntacticFunctionSymbol)lvs;
                    if(this.acSig.contains(lValSymb)) {
                    ((List<PairOfACTerms>)this.acProblems.get(lValSymb)).add(PairOfACTerms.create(lVal, rVal));
                    }
                    else {
                    /* free symbol */
                    if(lVal.length() > rVal.length()) {
                        ACTerm tmp = lVal;
                        lVal = rVal;
                        rVal = tmp;
                        tmp = lRep;
                        lRep = rRep;
                        rRep = tmp;
                    }
                    /* |lVal| <= |rVal| */
                    this.setValue(rRep, lRep);
                    this.todo.add(PairOfACTerms.create(lVal, rVal));
                    }
                }
                }
            }
            }
        }
        }
    }
    }


    /** Determines whether their was a failure.
     */
    public boolean fail() {
    return this.Fail;
    }


    /** Determines whether there is a cycle in the quasi-solved part.
     */
    public boolean cycleCheck() {
    Set<ACTerm> reps = new HashSet<ACTerm>();
    Iterator i = this.value.keySet().iterator();
    while(i.hasNext()) {
        ACTerm t = (ACTerm)i.next();
        reps.add(this.getRep(t));
        ACTerm val = (ACTerm)this.value.get(t);
        if(!val.isVariable() && !val.isConstant()) {
            reps.addAll(this.getAllReps(val));
        }
    }
    Stack<ACTerm> stack = new Stack<ACTerm>();
    int stacked = 0;
    int num = reps.size();

    Map newcounter = new LinkedHashMap();
    i = reps.iterator();
    while(i.hasNext()) {
        ACTerm v = (ACTerm)i.next();
        Integer c = Integer.valueOf(this.getCounter(v));
        newcounter.put(v, c);
        if(this.getCounter(v) == 0) {
        /* no predecessor */
        stack.add(v);
        stacked++;
        i.remove();
        }
    }

    boolean failed = false;
    while(num!=stacked && !failed) {
        if(stack.isEmpty()) {
            /* every variable has a predecessor */
            failed = true;
        }
        else {
        ACTerm v = (ACTerm)stack.pop();
        this.update(v, newcounter);
        i = reps.iterator();
        while(i.hasNext()) {
            ACTerm w = (ACTerm)i.next();
            if(((Integer)newcounter.get(w)).intValue() == 0) {
            stack.add(w);
            stacked++;
            i.remove();
            }
        }
        }
    }

    return failed;
    }

    /* Returns a set of all representatives of variables of t */
    private Set<ACTerm> getAllReps(ACTerm t) {
    Set<ACTerm> res = new HashSet<ACTerm>();
    Enumeration e = t.getVars().elements();
    while(e.hasMoreElements()) {
        res.add(this.getRep((ACTerm)e.nextElement()));
    }
    return res;
    }

    /* Decrement counter of reps */
    private void update(ACTerm v, Map newcounter) {
    ACTerm val = (ACTerm)this.value.get(v);
    if(val!=null && !val.isVariable() && !val.isConstant()) {
        MultisetOfACTerms vars = ((ACTerm)this.value.get(v)).getVars();
        Enumeration e = vars.elements();
        while(e.hasMoreElements()) {
        ACTerm w = (ACTerm)e.nextElement();
            ACTerm rep = this.getRep(w);
            newcounter.put(rep, Integer.valueOf(((Integer)newcounter.get(rep)).intValue() - vars.numberOfOccurences(w)));
        }
    }
    }


    /** Returns the pure problems belonging to f after transforming them with the
     * quasi-solved problems and deletes the pure problem.
     */
    public List<PairOfACTerms> getTransformed(SyntacticFunctionSymbol f) {
    List<PairOfACTerms> orig = (List<PairOfACTerms>)this.acProblems.get(f);
    if(orig.isEmpty()) {
        return orig;
    }
    this.walkThrough(f);
    return this.getAndDeleteACProblems(f);
    }

    /* variables in the quasi solved problems of f are replaced by their
     * representatives */
    private void walkThrough(SyntacticFunctionSymbol f) {
    Iterator i = this.value.keySet().iterator();

    /* quasi solved part */
    while(i.hasNext()) {
        ACTerm var = (ACTerm)i.next();
        ACTerm val = (ACTerm)this.value.get(var);
        if(val.getSymbol().equals(f)) {
        MultisetOfACTerms args = val.getMultiargs();
        MultisetOfACTerms newargs = MultisetOfACTerms.create();
        Enumeration e = args.elements();
        while(e.hasMoreElements()) {
            ACTerm elem = (ACTerm)e.nextElement();
            if(elem.isVariable()) {
                newargs.add(this.getRep(elem), args.numberOfOccurences(elem));
            }
            else {
            newargs.add(elem, args.numberOfOccurences(elem));
            }
        }
        this.value.put(var, ACTerm.create(f, newargs, this.acSig));
        }

    }
    }

    /* replace variables by their representatives, apply E-Rep as long
     * as possible */
    private List<PairOfACTerms> getAndDeleteACProblems(SyntacticFunctionSymbol f) {
    List<PairOfACTerms> orig = (List<PairOfACTerms>)this.acProblems.get(f);
    this.acProblems.put(f, new Vector<PairOfACTerms>());

    List<PairOfACTerms> res = new Vector<PairOfACTerms>();

    Iterator i = orig.iterator();
    while(i.hasNext()) {
        PairOfACTerms p = (PairOfACTerms)i.next();

        ACTerm l = this.ERep(p.getLeft(), f);
        ACTerm r = this.ERep(p.getRight(), f);

        res.add(PairOfACTerms.create(l, r));
    }

    return res;
    }

    /* replace vars by representatives and apply ERep */
    private ACTerm ERep(ACTerm t, SyntacticFunctionSymbol f) {
    /* replace vars by representatives */
    MultisetOfACTerms args = t.getMultiargs();
    MultisetOfACTerms newargs = MultisetOfACTerms.create();
    Enumeration e = args.elements();
    while(e.hasMoreElements()) {
        ACTerm elem = (ACTerm)e.nextElement();
        if(elem.isVariable()) {
            newargs.add(this.getRep(elem), args.numberOfOccurences(elem));
        }
        else {
            newargs.add(elem, args.numberOfOccurences(elem));
        }
    }
    /* apply E-Rep steps as long as possible */
    boolean changed = true;
    MultisetOfACTerms newerargs = null;
    while(changed) {
        changed = false;
        e = newargs.elements();
        newerargs = MultisetOfACTerms.create();
        while(e.hasMoreElements()) {
            ACTerm elem = (ACTerm)e.nextElement();
            ACTerm val = (ACTerm)this.value.get(elem);
            int n = newargs.numberOfOccurences(elem);
        if(val!=null && val.getSymbol().equals(f)) {
            changed = true;
            /* add arguments */
            MultisetOfACTerms valargs = val.getMultiargs();
            Enumeration e2 = valargs.elements();
            while(e2.hasMoreElements()) {
                ACTerm var = (ACTerm)e2.nextElement();
                newerargs.add(var, n*valargs.numberOfOccurences(var));
            }
        }
        else {
            newerargs.add(elem, n);
        }
        }
        if(changed) {
        newargs = newerargs;
        }
    }

    return ACTerm.create(f, newargs, this.acSig);
    }


    /** Transforms this problem into a substitution if it is solved.
     */
    public AlgebraSubstitution toSubst() {
    this.walkThrough();
    List<PairOfACTerms> pairs = this.Rep();

    AlgebraSubstitution res = AlgebraSubstitution.create();
    Iterator i = pairs.iterator();
    while(i.hasNext()) {
        PairOfACTerms p = (PairOfACTerms)i.next();
        AlgebraTerm l = p.getLeft().toTerm();
        if(this.freeVars.contains(l)) {
        res.put((VariableSymbol)((AlgebraVariable)l).getSymbol(), p.getRight().toTerm());
        }
    }

    return res;
    }

    /* variables in the quasi solved problems are replaced by their
     * representatives */
    private void walkThrough() {
    Iterator i = this.value.keySet().iterator();

    /* quasi solved part */
    while(i.hasNext()) {
        ACTerm var = (ACTerm)i.next();
        ACTerm val = (ACTerm)this.value.get(var);
        this.value.put(var, this.walkRec(val));
    }
    }

    /* recursive function that replaces variables by their representatives */
    private ACTerm walkRec(ACTerm val) {
    if(val.isVariable()) {
        return this.getRep(val);
    }
    if(val.isConstant()) {
        return val;
    }
    else {
        SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)val.getSymbol();
        if(val.hasArgs()) {
        List<ACTerm> args = val.getArgs();
        Vector<ACTerm> newargs = new Vector<ACTerm>();
        Iterator i = args.iterator();
        while(i.hasNext()) {
            newargs.add(this.walkRec((ACTerm)i.next()));
        }
        return ACTerm.create(f, newargs, this.acSig);
        }
        else {
        MultisetOfACTerms args = val.getMultiargs();
            MultisetOfACTerms newargs = MultisetOfACTerms.create();
        Enumeration e = args.elements();
        while(e.hasMoreElements()) {
            ACTerm elem = (ACTerm)e.nextElement();
            newargs.add(this.walkRec(elem), args.numberOfOccurences(elem));
        }
        return ACTerm.create(f, newargs, this.acSig);
        }
    }
    }

    /* apply Rep steps as long as possible */
    private List<PairOfACTerms> Rep() {
    boolean changed = true;
    while(changed) {
        changed = this.repStep();
    }

    List<PairOfACTerms> res = new Vector<PairOfACTerms>();
    Iterator i = this.value.keySet().iterator();
    while(i.hasNext()) {
        ACTerm var = (ACTerm)i.next();
        res.add(PairOfACTerms.create(var, (ACTerm)this.value.get(var)));
    }
    return res;
    }


    /* performs one replacement step and returns whether something was changed */
    private boolean repStep() {
    boolean res = false;

    Iterator i = this.value.keySet().iterator();
    while(i.hasNext()) {
        ACTerm var = (ACTerm)i.next();
        ACTerm val = (ACTerm)this.value.get(var);
        res = res || this.repAll(var, val);
    }

    return res;
    }

    /* replace all occurences of var on a rhs by val */
    private boolean repAll(ACTerm var, ACTerm val) {
    boolean res = false;
    Iterator i = this.value.keySet().iterator();
    while(i.hasNext()) {
        ACTerm othervar = (ACTerm)i.next();
        if(!var.equals(othervar)) {
        ACTerm orig = (ACTerm)this.value.get(othervar);
        BetterBoolean flag = new BetterBoolean(false);
        ACTerm trans = this.repRec(var, val, orig, flag);
        if(flag.booleanValue()) {
            /* something changed */
            res = true;
            this.value.put(othervar, trans);
        }
        }
    }

    return res;
    }

    /* recursive function that replaces a variables by a term */
    private ACTerm repRec(ACTerm var, ACTerm val, ACTerm orig, BetterBoolean flag) {
    if(orig.isVariable()) {
        if(orig.equals(var)) {
        flag.setValue(true);
        return val;
        }
        else {
            return orig;
        }
    }

    SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)orig.getSymbol();
    if(orig.hasArgs()) {
        List<ACTerm> args = orig.getArgs();
        Vector<ACTerm> newargs = new Vector<ACTerm>();
        Iterator i = args.iterator();
        while(i.hasNext()) {
        newargs.add(this.repRec(var, val, (ACTerm)i.next(), flag));
        }
        return ACTerm.create(f, newargs, this.acSig);
    }
    else {
        MultisetOfACTerms args = orig.getMultiargs();
        MultisetOfACTerms newargs = MultisetOfACTerms.create();
        Enumeration e = args.elements();
        while(e.hasMoreElements()) {
        ACTerm elem = (ACTerm)e.nextElement();
        ACTerm newelem = this.repRec(var, val, elem, flag);
        if(!newelem.getSymbol().equals(f)) {
            newargs.add(newelem, args.numberOfOccurences(elem));
        }
        else {
            /* flatten */
            int n = args.numberOfOccurences(elem);
            MultisetOfACTerms newestargs = newelem.getMultiargs();
            Enumeration e2 = newestargs.elements();
            while(e2.hasMoreElements()) {
            ACTerm newestelem = (ACTerm)e2.nextElement();
            newargs.add(newestelem, n*newestargs.numberOfOccurences(newestelem));
            }
        }

        }
        return ACTerm.create(f, newargs, this.acSig);
    }
    }


    /* Get the representative of the variable x */
    private ACTerm getRep(ACTerm x) {
    Object o = this.value.get(x);
    if(o==null) {
        return x;
    }
    ACTerm ot = (ACTerm)o;
    if(!ot.isVariable()) {
        return x;
    }
    else {
        return this.getRep(ot);
    }
    }

    /* Store val in x's value field */
    private void setValue(ACTerm x, ACTerm val) {
    ACTerm old = (ACTerm)this.value.get(x);
    if(old==null && !val.isVariable()) {
        /* noting yet ==> initialize counter */
        MultisetOfACTerms vars = val.getVars();
        Enumeration e = vars.elements();
        while(e.hasMoreElements()) {
        ACTerm v = (ACTerm)e.nextElement();
        this.incCounter(this.getRep(v), vars.numberOfOccurences(v));
        }
    }
    else if(old!=null && !old.isVariable()) {
        /* decrement for old */
        MultisetOfACTerms vars = old.getVars();
        Enumeration e = vars.elements();
        while(e.hasMoreElements()) {
        ACTerm v = (ACTerm)e.nextElement();
        this.decCounter(this.getRep(v), vars.numberOfOccurences(v));
        }
    }
    if(val.isVariable() && !x.equals(val)) {
         this.incCounter(this.getRep(val), this.getCounter(x));
         this.zeroCounter(this.getRep(x));
    }
    this.value.put(x, val);
    }

    private void incCounter(ACTerm v, int inc) {
    Object o = this.counter.get(v);
    int res = inc;
    if(o!=null) {
        res += ((Integer)o).intValue();
    }
    this.counter.put(v, Integer.valueOf(res));
    }

    private void decCounter(ACTerm v, int dec) {
    Object o = this.counter.get(v);
    int res = -dec;
    if(o!=null) {
        res += ((Integer)o).intValue();
    }
    if(res < 0) {
        res = 0;
    }
    this.counter.put(v, Integer.valueOf(res));
    }

    private int getCounter(ACTerm v) {
    Object o = this.counter.get(v);
    if(o==null) {
        return 0;
    }
    else {
        return ((Integer)o).intValue();
    }
    }

    private void zeroCounter(ACTerm v) {
    this.counter.put(v, Integer.valueOf(0));
    }

    @Override
    public String toString() {
    StringBuffer res = new StringBuffer();
    res.append("Value: " + this.value.toString() + "\n");
    res.append("Counter: " + this.counter.toString() + "\n");
    res.append("AC problems: " + this.acProblems.toString() + "\n");
    return res.toString();
    }

}
