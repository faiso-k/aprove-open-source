package aprove.verification.oldframework.Unification.Problems;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Unification.Utility.*;
import aprove.verification.oldframework.Utility.*;

/**
 *  Representation of a general ACnC-unification problem.
 *  <p>
 *  This is basically an extension of the general AC unification algorithm of
 *  <br>
 *  A. Boudet: "Competing for the AC-Unification Race", JAR 11, pp. 185-212
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class GeneralACnCProblem {

    private Set<AlgebraVariable> freeVars;
    private Set<AlgebraVariable> absVars;       // abstraction variables
    private Stack<PairOfACnCTerms> todo;
    private Map value;                    // value field for variables
    private Map counter;                  // counter for occur check
    private Map acProblems;               // problems for each ac symbol
    private Map cProblems;                // problems for each c symbol
    private Set<SyntacticFunctionSymbol> acSig;   // the ac symbols
    private Set<SyntacticFunctionSymbol> cSig;    // the c symbols
    private boolean Fail;                 // did we fail?
    private FreshVarGenerator fvg;


    private GeneralACnCProblem(Set<SyntacticFunctionSymbol> acSig, Set<SyntacticFunctionSymbol> cSig, Set<AlgebraVariable> freeVars, Set<AlgebraVariable> W) {
    this.acSig = acSig;
    this.cSig = cSig;
    this.freeVars = freeVars;
    this.absVars = new HashSet<AlgebraVariable>();
    this.todo = new Stack<PairOfACnCTerms>();
    this.value = new LinkedHashMap();
    this.counter = new LinkedHashMap();
    this.acProblems = new LinkedHashMap();
    this.cProblems = new LinkedHashMap();

    Iterator i = acSig.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)i.next();
        this.acProblems.put(fun, new Vector<PairOfACnCTerms>());
    }

    i = cSig.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)i.next();
        this.cProblems.put(fun, new Vector<PairOfACnCTerms>());
    }

    this.Fail = false;
    this.fvg = new FreshVarGenerator(W, FreshNameGenerator.TYPE_INFERENCE);
    }

    private GeneralACnCProblem() {
    super();
    }

    public GeneralACnCProblem shallowcopy() {
    GeneralACnCProblem res = new GeneralACnCProblem();
    res.acSig = this.acSig;
    res.cSig = this.cSig;
    res.freeVars = this.freeVars;
    res.absVars = new HashSet<AlgebraVariable>(this.absVars);
    res.todo = new Stack<PairOfACnCTerms>();
    res.value = new LinkedHashMap(this.value);
    res.counter = new LinkedHashMap(this.counter);
    res.acProblems = new LinkedHashMap();
    res.cProblems = new LinkedHashMap();
    Iterator i = this.acSig.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)i.next();
        res.acProblems.put(fun, new Vector<PairOfACnCTerms>((List<PairOfACnCTerms>)this.acProblems.get(fun)));
    }
    i = this.cSig.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)i.next();
        res.cProblems.put(fun, new Vector<PairOfACnCTerms>((List<PairOfACnCTerms>)this.cProblems.get(fun)));
    }
    res.Fail = this.Fail;
    res.fvg = this.fvg.shallowcopy();

    return res;
    }


    /** Creates a new GeneralACnCProblem where acSig specifies the function
     * symbols that are AC, cSig specifies the function symbols that are C, and freeVars are the free variables
     * occuring in the problem.
     */
    public static GeneralACnCProblem create(Set<SyntacticFunctionSymbol> acSig, Set<SyntacticFunctionSymbol> cSig, Set<AlgebraVariable> freeVars, Set<AlgebraVariable> W) {
    return new GeneralACnCProblem(acSig, cSig, freeVars, W);
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
    this.add(PairOfACnCTerms.create(ACnCTerm.create(s, this.acSig, this.cSig), ACnCTerm.create(t, this.acSig, this.cSig)));
    }


    /** Adds a set of equations to the problem.
     */
    public void addAll(Collection<PairOfACnCTerms> coll) {
    Iterator i = coll.iterator();
    while(i.hasNext()) {
        PairOfACnCTerms next = (PairOfACnCTerms)i.next();
        this.add(next);
    }
    }


    /** Add an equation (i.e. a PairOfACnCTerms) to the problem.
     */
    public void add(PairOfACnCTerms pair) {

    this.todo.push(pair);

    while(!this.todo.isEmpty() && !this.Fail) {
        PairOfACnCTerms p = (PairOfACnCTerms)this.todo.pop();
        ACnCTerm l = p.getLeft();
        ACnCTerm r = p.getRight();
        Symbol lSymb = l.getSymbol();
        Symbol rSymb = r.getSymbol();

        if(lSymb.equals(rSymb)) {
        if(lSymb instanceof SyntacticFunctionSymbol) {
            SyntacticFunctionSymbol lFunSymb = (SyntacticFunctionSymbol)lSymb;
            if(!this.acSig.contains(lFunSymb) && !this.cSig.contains(lFunSymb)) {
            /* decomposition for free theory */
            Enumeration i = l.elements();
            Enumeration j = r.elements();
            while(i.hasMoreElements()) {
                this.todo.push(PairOfACnCTerms.create((ACnCTerm)i.nextElement(), (ACnCTerm)j.nextElement()));
            }
            }
            else {
            /* apply variable abstraction */
            ExtVarAbstraction va = ExtVarAbstraction.create(l, this.fvg);
            va.extend(r, this.fvg);
            this.absVars.addAll(va.getRange());
            ACnCTerm newL = l.apply(va);
            ACnCTerm newR = r.apply(va);
            if(this.acSig.contains(lFunSymb)) {
                /* AC */
                ((List<PairOfACnCTerms>)this.acProblems.get(lSymb)).add(PairOfACnCTerms.create(newL, newR));
            }
            else {
                /* C */
                ((List<PairOfACnCTerms>)this.cProblems.get(lSymb)).add(PairOfACnCTerms.create(newL, newR));
            }
            Iterator i = va.getRange().iterator();
            while(i.hasNext()) {
                AlgebraVariable v = (AlgebraVariable)i.next();
                this.todo.add(PairOfACnCTerms.create(ACnCTerm.create(v, this.acSig, this.cSig), va.invGet(v)));
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
            ACnCTerm tmp1 = l;
            l = r;
            r = tmp1;
            Symbol tmp2 = lSymb;
            lSymb = rSymb;
            rSymb = tmp2;
            }
            /* lSymb is a variable symbol now */
            if(rSymb instanceof SyntacticFunctionSymbol) {
            SyntacticFunctionSymbol rFunSymb = (SyntacticFunctionSymbol)rSymb;
            if(this.acSig.contains(rFunSymb) || this.cSig.contains(rFunSymb)) {
                /* apply variable abstraction */
                ExtVarAbstraction va = ExtVarAbstraction.create(r, this.fvg);
                this.absVars.addAll(va.getRange());
                ACnCTerm r1 = r.apply(va);
                Iterator i = va.getRange().iterator();
                while(i.hasNext()) {
                    AlgebraVariable v = (AlgebraVariable)i.next();
                    this.todo.add(PairOfACnCTerms.create(ACnCTerm.create(v, this.acSig, this.cSig), va.invGet(v)));
                }
                Object o = this.value.get(l);
                if(o==null) {
                this.setValue(l, r1);
                }
                else {
                ACnCTerm val = (ACnCTerm)o;
                if(val.getSymbol() instanceof SyntacticFunctionSymbol) {
                    if(!val.getSymbol().equals(rSymb)) {
                        /* Conflict 2 */
                        this.Fail = true;
                    }
                    else {
                        this.todo.add(PairOfACnCTerms.create(r, val));
                    }
                }
                else {
                    /* val is a variable */
                    if(!val.equals(l)) {
                    /* different variable */
                            this.todo.add(PairOfACnCTerms.create(val, r1));
                    }
                }
                }
            }
            else {
                /* free symbol */
                /* apply variable abstraction */
                ExtVarAbstraction va = ExtVarAbstraction.create(r, this.fvg);
                this.absVars.addAll(va.getRange());
                ACnCTerm r1 = r.apply(va);
                Iterator i = va.getRange().iterator();
                while(i.hasNext()) {
                    AlgebraVariable v = (AlgebraVariable)i.next();
                    this.todo.add(PairOfACnCTerms.create(ACnCTerm.create(v, this.acSig, this.cSig), va.invGet(v)));
                }
                Object o = this.value.get(l);
                if(o==null) {
                this.setValue(l, r1);
                }
                else {
                ACnCTerm val = (ACnCTerm)o;
                if(val.getSymbol() instanceof SyntacticFunctionSymbol) {
                    if(!val.getSymbol().equals(rSymb)) {
                        /* Conflict 2 */
                        this.Fail = true;
                    }
                    else {
                    if(val.length() < r.length()) {
                        ACnCTerm tmp = val;
                        val = r;
                        r = tmp;
                    }
                    /* |r| <= |val| */
                        this.todo.add(PairOfACnCTerms.create(r, val));
                    }
                }
                else {
                    /* val is a variable */
                    if(!val.equals(l)) {
                    /* different variable */
                            this.todo.add(PairOfACnCTerms.create(val, r1));
                    }
                }
                }
            }
            }
            else {
            /* r is a variable */
            ACnCTerm lRep = this.getRep(l);
            ACnCTerm rRep = this.getRep(r);

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
                ACnCTerm lVal = (ACnCTerm)vl;
                ACnCTerm rVal = (ACnCTerm)vr;
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
                    ((List<PairOfACnCTerms>)this.acProblems.get(lValSymb)).add(PairOfACnCTerms.create(lVal, rVal));
                    }
                    else {
                    /* free symbol */
                    if(lVal.length() > rVal.length()) {
                        ACnCTerm tmp = lVal;
                        lVal = rVal;
                        rVal = tmp;
                        tmp = lRep;
                        lRep = rRep;
                        rRep = tmp;
                    }
                    /* |lVal| <= |rVal| */
                    this.setValue(rRep, lRep);
                    this.todo.add(PairOfACnCTerms.create(lVal, rVal));
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
    Set<ACnCTerm> reps = new HashSet<ACnCTerm>();
    Iterator i = this.value.keySet().iterator();
    while(i.hasNext()) {
        ACnCTerm t = (ACnCTerm)i.next();
        reps.add(this.getRep(t));
        ACnCTerm val = (ACnCTerm)this.value.get(t);
        if(!val.isVariable() && !val.isConstant()) {
            reps.addAll(this.getAllReps(val));
        }
    }
    Stack<ACnCTerm> stack = new Stack<ACnCTerm>();
    int stacked = 0;
    int num = reps.size();

    Map newcounter = new LinkedHashMap();
    i = reps.iterator();
    while(i.hasNext()) {
        ACnCTerm v = (ACnCTerm)i.next();
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
        ACnCTerm v = (ACnCTerm)stack.pop();
        this.update(v, newcounter);
        i = reps.iterator();
        while(i.hasNext()) {
            ACnCTerm w = (ACnCTerm)i.next();
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
    private Set<ACnCTerm> getAllReps(ACnCTerm t) {
    Set<ACnCTerm> res = new HashSet<ACnCTerm>();
    Enumeration e = t.getVars().elements();
    while(e.hasMoreElements()) {
        res.add(this.getRep((ACnCTerm)e.nextElement()));
    }
    return res;
    }

    /* Decrement counter of reps */
    private void update(ACnCTerm v, Map newcounter) {
    ACnCTerm val = (ACnCTerm)this.value.get(v);
    if(val!=null && !val.isVariable() && !val.isConstant()) {
        MultisetOfACnCTerms vars = ((ACnCTerm)this.value.get(v)).getVars();
        Enumeration e = vars.elements();
        while(e.hasMoreElements()) {
        ACnCTerm w = (ACnCTerm)e.nextElement();
            ACnCTerm rep = this.getRep(w);
            newcounter.put(rep, Integer.valueOf(((Integer)newcounter.get(rep)).intValue() - vars.numberOfOccurences(w)));
        }
    }
    }


    /** Returns the pure problems belonging to f after transforming them with the
     * quasi-solved problems and deletes the pure problem.
     */
    public List<PairOfACnCTerms> getTransformed(SyntacticFunctionSymbol f) {
    List<PairOfACnCTerms> orig;
    if(this.acSig.contains(f)) {
        orig = (List<PairOfACnCTerms>)this.acProblems.get(f);
    }
    else {
        orig = (List<PairOfACnCTerms>)this.cProblems.get(f);
    }
    if(orig.isEmpty()) {
        return orig;
    }
    this.walkThrough(f);
    return this.getAndDeleteACnCProblems(f);
    }

    /* variables in the quasi solved problems of f are replaced by their
     * representatives */
    private void walkThrough(SyntacticFunctionSymbol f) {
    Iterator i = this.value.keySet().iterator();

    /* quasi solved part */
    while(i.hasNext()) {
        ACnCTerm var = (ACnCTerm)i.next();
        ACnCTerm val = (ACnCTerm)this.value.get(var);
        if(val.getSymbol().equals(f)) {
        MultisetOfACnCTerms args = val.getMultiargs();
        MultisetOfACnCTerms newargs = MultisetOfACnCTerms.create();
        Enumeration e = args.elements();
        while(e.hasMoreElements()) {
            ACnCTerm elem = (ACnCTerm)e.nextElement();
            if(elem.isVariable()) {
                newargs.add(this.getRep(elem), args.numberOfOccurences(elem));
            }
            else {
            newargs.add(elem, args.numberOfOccurences(elem));
            }
        }
        this.value.put(var, ACnCTerm.create(f, newargs, this.acSig, this.cSig));
        }

    }
    }

    /* replace variables by their representatives, apply E-Rep as long
     * as possible */
    private List<PairOfACnCTerms> getAndDeleteACnCProblems(SyntacticFunctionSymbol f) {

    if(this.cSig.contains(f)) {
        /* nothing to be done for C */
        List<PairOfACnCTerms> orig = (List<PairOfACnCTerms>)this.cProblems.get(f);
        this.cProblems.put(f, new Vector<PairOfACnCTerms>());
        return orig;
    }

    List<PairOfACnCTerms> orig = (List<PairOfACnCTerms>)this.acProblems.get(f);
    this.acProblems.put(f, new Vector<PairOfACnCTerms>());

    List<PairOfACnCTerms> res = new Vector<PairOfACnCTerms>();

    Iterator i = orig.iterator();
    while(i.hasNext()) {
        PairOfACnCTerms p = (PairOfACnCTerms)i.next();

        ACnCTerm l = this.ERep(p.getLeft(), f);
        ACnCTerm r = this.ERep(p.getRight(), f);

        res.add(PairOfACnCTerms.create(l, r));
    }

    return res;
    }

    /* replace vars by representatives and apply ERep */
    private ACnCTerm ERep(ACnCTerm t, SyntacticFunctionSymbol f) {
    /* replace vars by representatives */
    MultisetOfACnCTerms args = t.getMultiargs();
    MultisetOfACnCTerms newargs = MultisetOfACnCTerms.create();
    Enumeration e = args.elements();
    while(e.hasMoreElements()) {
        ACnCTerm elem = (ACnCTerm)e.nextElement();
        if(elem.isVariable()) {
            newargs.add(this.getRep(elem), args.numberOfOccurences(elem));
        }
        else {
            newargs.add(elem, args.numberOfOccurences(elem));
        }
    }
    /* apply E-Rep steps as long as possible */
    boolean changed = true;
    MultisetOfACnCTerms newerargs = null;
    while(changed) {
        changed = false;
        e = newargs.elements();
        newerargs = MultisetOfACnCTerms.create();
        while(e.hasMoreElements()) {
            ACnCTerm elem = (ACnCTerm)e.nextElement();
            ACnCTerm val = (ACnCTerm)this.value.get(elem);
            int n = newargs.numberOfOccurences(elem);
        if(val!=null && val.getSymbol().equals(f)) {
            changed = true;
            /* add arguments */
            MultisetOfACnCTerms valargs = val.getMultiargs();
            Enumeration e2 = valargs.elements();
            while(e2.hasMoreElements()) {
                ACnCTerm var = (ACnCTerm)e2.nextElement();
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

    return ACnCTerm.create(f, newargs, this.acSig, this.cSig);
    }


    /** Transforms this problem into a substitution if it is solved.
     */
    public AlgebraSubstitution toSubst() {
    this.walkThrough();
    List<PairOfACnCTerms> pairs = this.Rep();

    AlgebraSubstitution res = AlgebraSubstitution.create();
    Iterator i = pairs.iterator();
    while(i.hasNext()) {
        PairOfACnCTerms p = (PairOfACnCTerms)i.next();
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
        ACnCTerm var = (ACnCTerm)i.next();
        ACnCTerm val = (ACnCTerm)this.value.get(var);
        this.value.put(var, this.walkRec(val));
    }
    }

    /* recursive function that replaces variables by their representatives */
    private ACnCTerm walkRec(ACnCTerm val) {
    if(val.isVariable()) {
        return this.getRep(val);
    }
    if(val.isConstant()) {
        return val;
    }
    else {
        SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)val.getSymbol();
        if(val.hasArgs()) {
        List<ACnCTerm> args = val.getArgs();
        Vector<ACnCTerm> newargs = new Vector<ACnCTerm>();
        Iterator i = args.iterator();
        while(i.hasNext()) {
            newargs.add(this.walkRec((ACnCTerm)i.next()));
        }
        return ACnCTerm.create(f, newargs, this.acSig, this.cSig);
        }
        else {
        MultisetOfACnCTerms args = val.getMultiargs();
            MultisetOfACnCTerms newargs = MultisetOfACnCTerms.create();
        Enumeration e = args.elements();
        while(e.hasMoreElements()) {
            ACnCTerm elem = (ACnCTerm)e.nextElement();
            newargs.add(this.walkRec(elem), args.numberOfOccurences(elem));
        }
        return ACnCTerm.create(f, newargs, this.acSig, this.cSig);
        }
    }
    }

    /* apply Rep steps as long as possible */
    private List<PairOfACnCTerms> Rep() {
    boolean changed = true;
    while(changed) {
        changed = this.repStep();
    }

    List<PairOfACnCTerms> res = new Vector<PairOfACnCTerms>();
    Iterator i = this.value.keySet().iterator();
    while(i.hasNext()) {
        ACnCTerm var = (ACnCTerm)i.next();
        res.add(PairOfACnCTerms.create(var, (ACnCTerm)this.value.get(var)));
    }
    return res;
    }


    /* performs one replacement step and returns whether something was changed */
    private boolean repStep() {
    boolean res = false;

    Iterator i = this.value.keySet().iterator();
    while(i.hasNext()) {
        ACnCTerm var = (ACnCTerm)i.next();
        ACnCTerm val = (ACnCTerm)this.value.get(var);
        res = res || this.repAll(var, val);
    }

    return res;
    }

    /* replace all occurences of var on a rhs by val */
    private boolean repAll(ACnCTerm var, ACnCTerm val) {
    boolean res = false;
    Iterator i = this.value.keySet().iterator();
    while(i.hasNext()) {
        ACnCTerm othervar = (ACnCTerm)i.next();
        if(!var.equals(othervar)) {
        ACnCTerm orig = (ACnCTerm)this.value.get(othervar);
        BetterBoolean flag = new BetterBoolean(false);
        ACnCTerm trans = this.repRec(var, val, orig, flag);
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
    private ACnCTerm repRec(ACnCTerm var, ACnCTerm val, ACnCTerm orig, BetterBoolean flag) {
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
        List<ACnCTerm> args = orig.getArgs();
        Vector<ACnCTerm> newargs = new Vector<ACnCTerm>();
        Iterator i = args.iterator();
        while(i.hasNext()) {
        newargs.add(this.repRec(var, val, (ACnCTerm)i.next(), flag));
        }
        return ACnCTerm.create(f, newargs, this.acSig, this.cSig);
    }
    else {
        MultisetOfACnCTerms args = orig.getMultiargs();
        MultisetOfACnCTerms newargs = MultisetOfACnCTerms.create();
        Enumeration e = args.elements();
        while(e.hasMoreElements()) {
        ACnCTerm elem = (ACnCTerm)e.nextElement();
        ACnCTerm newelem = this.repRec(var, val, elem, flag);
        if(!newelem.getSymbol().equals(f)) {
            newargs.add(newelem, args.numberOfOccurences(elem));
        }
        else {
            /* flatten */
            int n = args.numberOfOccurences(elem);
            MultisetOfACnCTerms newestargs = newelem.getMultiargs();
            Enumeration e2 = newestargs.elements();
            while(e2.hasMoreElements()) {
            ACnCTerm newestelem = (ACnCTerm)e2.nextElement();
            newargs.add(newestelem, n*newestargs.numberOfOccurences(newestelem));
            }
        }

        }
        return ACnCTerm.create(f, newargs, this.acSig, this.cSig);
    }
    }


    /* Get the representative of the variable x */
    private ACnCTerm getRep(ACnCTerm x) {
    Object o = this.value.get(x);
    if(o==null) {
        return x;
    }
    ACnCTerm ot = (ACnCTerm)o;
    if(!ot.isVariable()) {
        return x;
    }
    else {
        return this.getRep(ot);
    }
    }

    /* Store val in x's value field */
    private void setValue(ACnCTerm x, ACnCTerm val) {
    ACnCTerm old = (ACnCTerm)this.value.get(x);
    if(old==null && !val.isVariable()) {
        /* noting yet ==> initialize counter */
        MultisetOfACnCTerms vars = val.getVars();
        Enumeration e = vars.elements();
        while(e.hasMoreElements()) {
        ACnCTerm v = (ACnCTerm)e.nextElement();
        this.incCounter(this.getRep(v), vars.numberOfOccurences(v));
        }
    }
    else if(old!=null && !old.isVariable()) {
        /* decrement for old */
        MultisetOfACnCTerms vars = old.getVars();
        Enumeration e = vars.elements();
        while(e.hasMoreElements()) {
        ACnCTerm v = (ACnCTerm)e.nextElement();
        this.decCounter(this.getRep(v), vars.numberOfOccurences(v));
        }
    }
    if(val.isVariable() && !x.equals(val)) {
         this.incCounter(this.getRep(val), this.getCounter(x));
         this.zeroCounter(this.getRep(x));
    }
    this.value.put(x, val);
    }

    private void incCounter(ACnCTerm v, int inc) {
    Object o = this.counter.get(v);
    int res = inc;
    if(o!=null) {
        res += ((Integer)o).intValue();
    }
    this.counter.put(v, Integer.valueOf(res));
    }

    private void decCounter(ACnCTerm v, int dec) {
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

    private int getCounter(ACnCTerm v) {
    Object o = this.counter.get(v);
    if(o==null) {
        return 0;
    }
    else {
        return ((Integer)o).intValue();
    }
    }

    private void zeroCounter(ACnCTerm v) {
    this.counter.put(v, Integer.valueOf(0));
    }

    @Override
    public String toString() {
    StringBuffer res = new StringBuffer();
    res.append("Value: " + this.value.toString() + "\n");
    res.append("Counter: " + this.counter.toString() + "\n");
    res.append("AC problems: " + this.acProblems.toString() + "\n");
    res.append("C problems: " + this.cProblems.toString() + "\n");
    return res.toString();
    }

}
