/*
 * Created on Feb 14, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Problems;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator;
import aprove.verification.oldframework.BasicStructures.*;
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

    private Set<TRSVariable> freeVars;
    private Set<TRSVariable> absVars;       // abstraction variables
    private Stack<PairOfACTerms> todo;
    private Map<ACTerm, ACTerm> value;                    // value field for variables
    private Map<ACTerm, Integer> counter;                  // counter for occur check
    private Map<FunctionSymbol, List<PairOfACTerms>> acProblems;               // problems for each ac symbol
    private Set<FunctionSymbol> acSig;   // the ac symbols
    private boolean Fail;                 // did we fail?
    private FreshVarGenerator fvg;


    private GeneralACProblem(Set<FunctionSymbol> acSig, Set<TRSVariable> freeVars, Set<TRSVariable> W) {
        this.acSig = acSig;
        this.freeVars = freeVars;
        this.absVars = new HashSet<TRSVariable>();
        this.todo = new Stack<PairOfACTerms>();
        this.value = new LinkedHashMap<ACTerm, ACTerm>();
        this.counter = new LinkedHashMap<ACTerm, Integer>();
        this.acProblems = new LinkedHashMap<FunctionSymbol, List<PairOfACTerms>>();

        for(FunctionSymbol fun : acSig) {
            this.acProblems.put(fun, new ArrayList<PairOfACTerms>());
        }

        this.Fail = false;
        this.fvg = new FreshVarGenerator(W);
    }

    private GeneralACProblem() {
        super();
    }

    public GeneralACProblem shallowcopy() {
        GeneralACProblem res = new GeneralACProblem();
        res.acSig = this.acSig;
        res.freeVars = this.freeVars;
        res.absVars = new HashSet<TRSVariable>(this.absVars);
        res.todo = new Stack<PairOfACTerms>();
        res.value = new LinkedHashMap<ACTerm, ACTerm>(this.value);
        res.counter = new LinkedHashMap<ACTerm, Integer>(this.counter);
        res.acProblems = new LinkedHashMap<FunctionSymbol, List<PairOfACTerms>>();
        for(FunctionSymbol fun : this.acSig) {
            res.acProblems.put(fun, new ArrayList<PairOfACTerms>(this.acProblems.get(fun)));
        }
        res.Fail = this.Fail;
        res.fvg = this.fvg;

        return res;
    }


    /** Creates a new GeneralACProblem where acSig specifies the function
     * symbols that are AC and freeVars are the free variables occuring in the problem.
     */
    public static GeneralACProblem create(Set<FunctionSymbol> acSig, Set<TRSVariable> freeVars, Set<TRSVariable> W) {
        return new GeneralACProblem(acSig, freeVars, W);
    }


    /** Returns the variables that were used for variable abstraction.
     */
    public Set<TRSVariable> getAbsVars() {
        return this.absVars;
    }

    /** Returns the fresh variable generator used by this problem.
     */
    public FreshVarGenerator getFreshVarGen() {
        return this.fvg;
    }


    /** Add an equation generated from s and t to the problem.
     */
    public void add(TRSTerm s, TRSTerm t) {
        this.add(PairOfACTerms.create(ACTerm.create(s, this.acSig), ACTerm.create(t, this.acSig)));
    }


    /** Adds a set of equations to the problem.
     */
    public void addAll(Collection<PairOfACTerms> coll) {
        for(PairOfACTerms next : coll) {
            this.add(next);
        }
    }


    /** Add an equation (i.e. a PairOfACTerms) to the problem.
     */
    private void add(PairOfACTerms pair) {

        this.todo.push(pair);

        while(!this.todo.isEmpty() && !this.Fail) {
            PairOfACTerms p = this.todo.pop();
            ACTerm l = p.getLeft();
            ACTerm r = p.getRight();
            FunctionSymbol lSymb = l.getSymbol();
            FunctionSymbol rSymb = r.getSymbol();

            if(((lSymb instanceof FunctionSymbol) && lSymb.equals(rSymb))
                    || ((lSymb == null) && (l.equals(r)))){
                if(lSymb != null) {
                    if(!this.acSig.contains(lSymb)) {
                        /* decomposition for free theory */
                        Iterator<ACTerm> i = l.elements().iterator();
                        Iterator<ACTerm> j = r.elements().iterator();
                        while(i.hasNext()) {
                            this.todo.push(PairOfACTerms.create(i.next(), j.next()));
                        }
                    }
                    else {
                        /* apply variable abstraction */
                        VarAbstraction va = VarAbstraction.create(l, this.fvg);
                        va.extend(r, this.fvg);
                        this.absVars.addAll(va.getRange());
                        ACTerm newL = l.apply(va);
                        ACTerm newR = r.apply(va);
                        this.acProblems.get(lSymb).add(PairOfACTerms.create(newL, newR));
                        for(TRSVariable v : va.getRange()) {
                            this.todo.add(PairOfACTerms.create(ACTerm.create(v, this.acSig), va.invGet(v)));
                        }
                    }
                }
                /* otherwise, they are equal variables and there's nothing to be done */
            }
            else {
                /* not equal */
                if((lSymb instanceof FunctionSymbol) && (rSymb instanceof FunctionSymbol)) {
                    /* Conflict 1, i.e. Clash */
                    this.Fail = true;
                }
                else {
                    if(!(lSymb == null)) {
                        /* swap */
                        ACTerm tmp1 = l;
                        l = r;
                        r = tmp1;
                        FunctionSymbol tmp2 = lSymb;
                        lSymb = rSymb;
                        rSymb = tmp2;
                    }
                    /* lSymb is a variable symbol now */
                    if(rSymb instanceof FunctionSymbol) {
                        if(this.acSig.contains(rSymb)) {
                            /* apply variable abstraction */
                            VarAbstraction va = VarAbstraction.create(r, this.fvg);
                            this.absVars.addAll(va.getRange());
                            ACTerm r1 = r.apply(va);
                            for(TRSVariable v : va.getRange()) {
                                this.todo.add(PairOfACTerms.create(ACTerm.create(v, this.acSig), va.invGet(v)));
                            }
                            ACTerm val = this.value.get(l);
                            if(val==null) {
                                this.setValue(l, r1);
                            }
                            else {
                                if(val.getSymbol() instanceof FunctionSymbol) {
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
                            /* rSymb is free symbol */
                            /* apply variable abstraction */
                            VarAbstraction va = VarAbstraction.create(r, this.fvg);
                            this.absVars.addAll(va.getRange());
                            ACTerm r1 = r.apply(va);
                            for(TRSVariable v : va.getRange()) {
                                this.todo.add(PairOfACTerms.create(ACTerm.create(v, this.acSig), va.invGet(v)));
                            }
                            ACTerm val = this.value.get(l);
                            if(val==null) {
                                this.setValue(l, r1);
                            }
                            else {
                                if(val.getSymbol() instanceof FunctionSymbol) {
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
                            ACTerm lVal = this.value.get(lRep);
                            ACTerm rVal = this.value.get(rRep);
                            if(lVal==null) {
                                this.setValue(lRep, rRep);
                            }
                            else if(rVal==null) {
                                this.setValue(rRep, lRep);
                            }
                            else {
                                FunctionSymbol lvs = lVal.getSymbol();
                                FunctionSymbol rvs = rVal.getSymbol();
                                if(!(((lvs instanceof FunctionSymbol) && lvs.equals(rvs))
                                        || ((lvs == null) && (lVal.equals(rVal))))){
                                    /* Conflict 2, i.e. Clash */
                                    this.Fail = true;
                                }
                                else {
                                    /* equal function symbols */
                                    if(lvs !=null) {
                                        FunctionSymbol lValSymb = (FunctionSymbol)lvs;
                                        if(this.acSig.contains(lValSymb)) {
                                            ((List<PairOfACTerms>)this.acProblems.get(lValSymb)).add(PairOfACTerms.create(lVal, rVal));
                                        }
                                    }
                                    if(lvs == null || !this.acSig.contains(lvs)) {
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
        for(ACTerm t : this.value.keySet()) {
            reps.add(this.getRep(t));
            ACTerm val = this.value.get(t);
            if(!val.isVariable() && !val.isConstant()) {
                reps.addAll(this.getAllReps(val));
            }
        }
        Stack<ACTerm> stack = new Stack<ACTerm>();
        int stacked = 0;
        int num = reps.size();

        Map<ACTerm, Integer> newcounter = new LinkedHashMap<ACTerm, Integer>();
        Iterator i = reps.iterator();
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
                    if((newcounter.get(w)).intValue() == 0) {
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
        for (ACTerm term : t.getVars().elements()) {
            res.add(this.getRep(term));
        }
        return res;
    }

    /* Decrement counter of reps */
    private void update(ACTerm v, Map<ACTerm, Integer> newcounter) {
        ACTerm val = this.value.get(v);
        if(val!=null && !val.isVariable() && !val.isConstant()) {
            MultisetOfACTerms vars = this.value.get(v).getVars();
            for (ACTerm w : vars.elements()) {
                ACTerm rep = this.getRep(w);
                newcounter.put(rep, Integer.valueOf(newcounter.get(rep).intValue() - vars.numberOfOccurences(w)));
            }
        }
    }


    /** Returns the pure problems belonging to f after transforming them with the
     * quasi-solved problems and deletes the pure problem.
     */
    public List<PairOfACTerms> getTransformed(FunctionSymbol f) {
        List<PairOfACTerms> orig = this.acProblems.get(f);
        if(orig.isEmpty()) {
            return orig;
        }
        this.walkThrough(f);
        return this.getAndDeleteACProblems(f);
    }

    /* variables in the quasi solved problems of f are replaced by their
     * representatives */
    private void walkThrough(FunctionSymbol f) {
        if(Globals.useAssertions) {
            assert f != null;
        }
        /* quasi solved part */
        for(ACTerm var : this.value.keySet()) {
            ACTerm val = this.value.get(var);
            if(f.equals(val.getSymbol())) {
                MultisetOfACTerms args = val.getMultiargs();
                ArrayList<ACTerm> newargs = new ArrayList<ACTerm>();
                for (ACTerm elem : args.elements()) {
                    if(elem.isVariable()) {
                        for(int i=0;i<args.numberOfOccurences(elem);i++) {
                            newargs.add(this.getRep(elem));
                        }
                    }
                    else {
                        for(int i=0;i<args.numberOfOccurences(elem);i++) {
                            newargs.add(elem);
                        }
                    }
                }
                this.value.put(var, ACTerm.create(f, MultisetOfACTerms.create(newargs), this.acSig));
            }
        }
    }

    /* replace variables by their representatives, apply E-Rep as long
     * as possible */
    private List<PairOfACTerms> getAndDeleteACProblems(FunctionSymbol f) {
        List<PairOfACTerms> orig = this.acProblems.get(f);
        this.acProblems.put(f, new ArrayList<PairOfACTerms>());

        List<PairOfACTerms> res = new ArrayList<PairOfACTerms>();

        for(PairOfACTerms p : orig) {

            ACTerm l = this.ERep(p.getLeft(), f);
            ACTerm r = this.ERep(p.getRight(), f);

            res.add(PairOfACTerms.create(l, r));
        }

        return res;
    }

    /* replace vars by representatives and apply ERep */
    private ACTerm ERep(ACTerm t, FunctionSymbol f) {
        if(Globals.useAssertions) {
            assert f != null;
        }
        /* replace vars by representatives */
        MultisetOfACTerms args = t.getMultiargs();
        ArrayList<ACTerm> newargs = new ArrayList<ACTerm>();
        for (ACTerm elem : args.elements()) {
            if(elem.isVariable()) {
                for(int i=0;i<args.numberOfOccurences(elem);i++) {
                    newargs.add(this.getRep(elem));
                }
            }
            else {
                for(int i=0;i<args.numberOfOccurences(elem);i++) {
                    newargs.add(elem);
                }
            }
        }
        /* apply E-Rep steps as long as possible */
        boolean changed = true;
        ArrayList<ACTerm> newerargs = null;
        while(changed) {
            changed = false;
            newerargs = new ArrayList<ACTerm>();
            for (ACTerm elem : newargs) {
                ACTerm val = this.value.get(elem);
                int n = 0;
                for(ACTerm elemOcc : newargs) {
                    if(elemOcc.equals(elem)) {
                        n++;
                    }
                }
                if(val!=null && f.equals(val.getSymbol())) {
                    changed = true;
                    /* add arguments */
                    MultisetOfACTerms valargs = val.getMultiargs();
                    for (ACTerm var : valargs.elements()) {
                        for(int i=0; i<n*valargs.numberOfOccurences(var);i++) {
                            newerargs.add(elem);
                        }
                    }
                }
                else {
                    for(int i=0; i<n;i++) {
                        newerargs.add(elem);
                    }
                }
            }
            if(changed) {
                newargs = newerargs;
            }
        }

        return ACTerm.create(f, MultisetOfACTerms.create(newargs), this.acSig);
    }


    /** Transforms this problem into a substitution if it is solved.
     */
    public TRSSubstitution toSubst() {
        this.walkThrough();
        List<PairOfACTerms> pairs = this.Rep();

        TRSSubstitution res = TRSSubstitution.create();
        for(PairOfACTerms p : pairs) {
            TRSTerm l = p.getLeft().toTerm();
            if(this.freeVars.contains(l)) {
                res = res.extend(TRSSubstitution.create((TRSVariable)l, p.getRight().toTerm()));
            }
        }

        return res;
    }

    /* variables in the quasi solved problems are replaced by their
     * representatives */
    private void walkThrough() {
        /* quasi solved part */
        for(ACTerm var:this.value.keySet()) {
            ACTerm val = this.value.get(var);
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
            FunctionSymbol f = val.getSymbol();
            if(val.hasArgs()) {
                List<ACTerm> args = val.getArgs();
                ArrayList<ACTerm> newargs = new ArrayList<ACTerm>();
                for(ACTerm arg:args) {
                    newargs.add(this.walkRec(arg));
                }
                return ACTerm.create(f, newargs, this.acSig);
            }
            else {
                MultisetOfACTerms args = val.getMultiargs();
                ArrayList<ACTerm> newargs = new ArrayList<ACTerm>();
                for(ACTerm elem:args.elements()) {
                    ACTerm newEl = this.walkRec(elem);
                    for(int i=0;i<args.numberOfOccurences(elem);i++) {
                        newargs.add(newEl);
                    }
                }
                return ACTerm.create(f, MultisetOfACTerms.create(newargs), this.acSig);
            }
        }
    }

    /* apply Rep steps as long as possible */
    private List<PairOfACTerms> Rep() {
        boolean changed = true;
        while(changed) {
            changed = this.repStep();
        }

        List<PairOfACTerms> res = new ArrayList<PairOfACTerms>();
        for(ACTerm var:this.value.keySet()) {
            res.add(PairOfACTerms.create(var, this.value.get(var)));
        }
        return res;
    }


    /* performs one replacement step and returns whether something was changed */
    private boolean repStep() {
        boolean res = false;

        for(ACTerm var:this.value.keySet()) {
            ACTerm val = this.value.get(var);
            res = res || this.repAll(var, val);
        }

        return res;
    }

    /* replace all occurences of var on a rhs by val */
    private boolean repAll(ACTerm var, ACTerm val) {
        boolean res = false;
        for(ACTerm othervar:this.value.keySet()) {
            if(!var.equals(othervar)) {
                ACTerm orig = this.value.get(othervar);
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

        FunctionSymbol f = orig.getSymbol();
        if(orig.hasArgs()) {
            List<ACTerm> args = orig.getArgs();
            ArrayList<ACTerm> newargs = new ArrayList<ACTerm>();
            for(ACTerm i:args) {
                newargs.add(this.repRec(var, val, i, flag));
            }
            return ACTerm.create(f, newargs, this.acSig);
        }
        else {
            MultisetOfACTerms args = orig.getMultiargs();
            ArrayList<ACTerm> newargs = new ArrayList<ACTerm>();
            for (ACTerm elem : args.elements()) {
                ACTerm newelem = this.repRec(var, val, elem, flag);
                if(!f.equals(newelem.getSymbol())) {
                    for(int i=0;i<args.numberOfOccurences(elem);i++) {
                        newargs.add(newelem);
                    }
                }
                else {
                    /* flatten */
                    int n = args.numberOfOccurences(elem);
                    MultisetOfACTerms newestargs = newelem.getMultiargs();
                    for (ACTerm newestelem : newestargs.elements()) {
                        for(int i=0;i<n*newestargs.numberOfOccurences(newestelem);i++) {
                            newargs.add(newestelem);
                        }
                    }
                }
            }
            return ACTerm.create(f, MultisetOfACTerms.create(newargs), this.acSig);
        }
    }


    /* Get the representative of the variable x */
    private ACTerm getRep(ACTerm x) {
        ACTerm ot = this.value.get(x);
        if(ot==null) {
            return x;
        }
        if(!ot.isVariable()) {
            return x;
        }
        else {
            return this.getRep(ot);
        }
    }

    /* Store val in x's value field */
    private void setValue(ACTerm x, ACTerm val) {
        ACTerm old = this.value.get(x);
        if(old==null && !val.isVariable()) {
            /* noting yet ==> initialize counter */
            MultisetOfACTerms vars = val.getVars();
            for (ACTerm v : vars.elements()) {
                this.incCounter(this.getRep(v), vars.numberOfOccurences(v));
            }
        }
        else if(old!=null && !old.isVariable()) {
            /* decrement for old */
            MultisetOfACTerms vars = old.getVars();
            for (ACTerm v : vars.elements()) {
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
        Integer o = this.counter.get(v);
        int res = inc;
        if(o!=null) {
            res += o.intValue();
        }
        this.counter.put(v, Integer.valueOf(res));
    }

    private void decCounter(ACTerm v, int dec) {
        Integer o = this.counter.get(v);
        int res = -dec;
        if(o!=null) {
            res += o.intValue();
        }
        if(res < 0) {
            res = 0;
        }
        this.counter.put(v, Integer.valueOf(res));
    }

    private int getCounter(ACTerm v) {
        Integer o = this.counter.get(v);
        if(o==null) {
            return 0;
        }
        else {
            return o.intValue();
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

