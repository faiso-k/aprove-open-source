/*
 * Created on Feb 15, 2006
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

    private Set<TRSVariable> freeVars;
    private Set<TRSVariable> absVars;       // abstraction variables
    private Stack<PairOfACnCTerms> todo;
    private Map<ACnCTerm, ACnCTerm> value;                    // value field for variables
    private Map<ACnCTerm, Integer> counter;                  // counter for occur check
    private Map<FunctionSymbol, List<PairOfACnCTerms>> acProblems;               // problems for each ac symbol
    private Map<FunctionSymbol, List<PairOfACnCTerms>> cProblems;                // problems for each c symbol
    private Set<FunctionSymbol> acSig;   // the ac symbols
    private Set<FunctionSymbol> cSig;    // the c symbols
    private boolean Fail;                 // did we fail?
    private FreshVarGenerator fvg;


    private GeneralACnCProblem(Set<FunctionSymbol> acSig, Set<FunctionSymbol> cSig, Set<TRSVariable> freeVars, Set<TRSVariable> W) {
        this.acSig = acSig;
        this.cSig = cSig;
        this.freeVars = freeVars;
        this.absVars = new HashSet<TRSVariable>();
        this.todo = new Stack<PairOfACnCTerms>();
        this.value = new LinkedHashMap<ACnCTerm, ACnCTerm>();
        this.counter = new LinkedHashMap<ACnCTerm, Integer>();
        this.acProblems = new LinkedHashMap<FunctionSymbol, List<PairOfACnCTerms>>();
        this.cProblems = new LinkedHashMap<FunctionSymbol, List<PairOfACnCTerms>>();

        for(FunctionSymbol fun : acSig) {
            this.acProblems.put(fun, new ArrayList<PairOfACnCTerms>());
        }
        for(FunctionSymbol fun : cSig) {
            this.cProblems.put(fun, new ArrayList<PairOfACnCTerms>());
        }

        this.Fail = false;
        this.fvg = new FreshVarGenerator(W);
    }

    private GeneralACnCProblem() {
        super();
    }

    public GeneralACnCProblem shallowcopy() {
        GeneralACnCProblem res = new GeneralACnCProblem();
        res.acSig = this.acSig;
        res.cSig = this.cSig;
        res.freeVars = this.freeVars;
        res.absVars = new HashSet<TRSVariable>(this.absVars);
        res.todo = new Stack<PairOfACnCTerms>();
        res.value = new LinkedHashMap<ACnCTerm, ACnCTerm>(this.value);
        res.counter = new LinkedHashMap<ACnCTerm, Integer>(this.counter);
        res.acProblems = new LinkedHashMap<FunctionSymbol, List<PairOfACnCTerms>>();
        res.cProblems = new LinkedHashMap<FunctionSymbol, List<PairOfACnCTerms>>();
        for(FunctionSymbol fun : this.acSig) {
            res.acProblems.put(fun, new ArrayList<PairOfACnCTerms>(this.acProblems.get(fun)));
        }
        for(FunctionSymbol fun : this.cSig) {
            res.cProblems.put(fun, new ArrayList<PairOfACnCTerms>(this.cProblems.get(fun)));
        }
        res.Fail = this.Fail;
        res.fvg = this.fvg;

        return res;
    }


    /** Creates a new GeneralACnCProblem where acSig specifies the function
     * symbols that are AC, cSig specifies the function symbols that are C, and freeVars are the free variables
     * occuring in the problem.
     */
    public static GeneralACnCProblem create(Set<FunctionSymbol> acSig, Set<FunctionSymbol> cSig, Set<TRSVariable> freeVars, Set<TRSVariable> W) {
        return new GeneralACnCProblem(acSig, cSig, freeVars, W);
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
        this.add(PairOfACnCTerms.create(ACnCTerm.create(s, this.acSig, this.cSig), ACnCTerm.create(t, this.acSig, this.cSig)));
    }


    /** Adds a set of equations to the problem.
     */
    public void addAll(Collection<PairOfACnCTerms> coll) {
        for(PairOfACnCTerms next : coll) {
            this.add(next);
        }
    }


    /** Add an equation (i.e. a PairOfACnCTerms) to the problem.
     */
    private void add(PairOfACnCTerms pair) {

        this.todo.push(pair);

        while(!this.todo.isEmpty() && !this.Fail) {
            PairOfACnCTerms p = this.todo.pop();
            ACnCTerm l = p.getLeft();
            ACnCTerm r = p.getRight();
            FunctionSymbol lSymb = l.getSymbol();
            FunctionSymbol rSymb = r.getSymbol();

            if(((lSymb instanceof FunctionSymbol) && lSymb.equals(rSymb))
                    || ((lSymb == null) && (l.equals(r)))){
                if(lSymb != null) {
                    if(!this.acSig.contains(lSymb) && !this.cSig.contains(lSymb)) {
                        /* decomposition for free theory */
                        Iterator<ACnCTerm> i = l.elements().iterator();
                        Iterator<ACnCTerm> j = r.elements().iterator();
                        while(i.hasNext()) {
                            this.todo.push(PairOfACnCTerms.create(i.next(), j.next()));
                        }
                    }
                    else {
                        /* apply variable abstraction */
                        ExtVarAbstraction va = ExtVarAbstraction.create(l, this.fvg);
                        va.extend(r, this.fvg);
                        this.absVars.addAll(va.getRange());
                        ACnCTerm newL = l.apply(va);
                        ACnCTerm newR = r.apply(va);
                        if(this.acSig.contains(lSymb)) {
                            /* AC */
                            this.acProblems.get(lSymb).add(PairOfACnCTerms.create(newL, newR));
                        }
                        else {
                            /* C */
                            this.cProblems.get(lSymb).add(PairOfACnCTerms.create(newL, newR));
                        }
                        for(TRSVariable v : va.getRange()) {
                            this.todo.add(PairOfACnCTerms.create(ACnCTerm.create(v, this.acSig, this.cSig), va.invGet(v)));
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
                        ACnCTerm tmp1 = l;
                        l = r;
                        r = tmp1;
                        FunctionSymbol tmp2 = lSymb;
                        lSymb = rSymb;
                        rSymb = tmp2;
                    }
                    /* lSymb is a variable symbol now */
                    if(rSymb instanceof FunctionSymbol) {
                        if(this.acSig.contains(rSymb)|| this.cSig.contains(rSymb)) {
                            /* apply variable abstraction */
                            ExtVarAbstraction va = ExtVarAbstraction.create(r, this.fvg);
                            this.absVars.addAll(va.getRange());
                            ACnCTerm r1 = r.apply(va);
                            for(TRSVariable v : va.getRange()) {
                                this.todo.add(PairOfACnCTerms.create(ACnCTerm.create(v, this.acSig, this.cSig), va.invGet(v)));
                            }
                            ACnCTerm val = this.value.get(l);
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
                            /* rSymb is free symbol */
                            /* apply variable abstraction */
                            ExtVarAbstraction va = ExtVarAbstraction.create(r, this.fvg);
                            this.absVars.addAll(va.getRange());
                            ACnCTerm r1 = r.apply(va);
                            for(TRSVariable v : va.getRange()) {
                                this.todo.add(PairOfACnCTerms.create(ACnCTerm.create(v, this.acSig, this.cSig), va.invGet(v)));
                            }
                            ACnCTerm val = this.value.get(l);
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
                            ACnCTerm lVal = this.value.get(lRep);
                            ACnCTerm rVal = this.value.get(rRep);
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
                                            ((List<PairOfACnCTerms>)this.acProblems.get(lValSymb)).add(PairOfACnCTerms.create(lVal, rVal));
                                        }
                                    }
                                    if(lvs == null || !this.acSig.contains(lvs)) {
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
        for(ACnCTerm t : this.value.keySet()) {
            reps.add(this.getRep(t));
            ACnCTerm val = this.value.get(t);
            if(!val.isVariable() && !val.isConstant()) {
                reps.addAll(this.getAllReps(val));
            }
        }
        Stack<ACnCTerm> stack = new Stack<ACnCTerm>();
        int stacked = 0;
        int num = reps.size();

        Map<ACnCTerm, Integer> newcounter = new LinkedHashMap<ACnCTerm, Integer>();
        Iterator i = reps.iterator();
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
    private Set<ACnCTerm> getAllReps(ACnCTerm t) {
        Set<ACnCTerm> res = new HashSet<ACnCTerm>();
        for (ACnCTerm term : t.getVars().elements()) {
            res.add(this.getRep(term));
        }
        return res;
    }

    /* Decrement counter of reps */
    private void update(ACnCTerm v, Map<ACnCTerm, Integer> newcounter) {
        ACnCTerm val = this.value.get(v);
        if(val!=null && !val.isVariable() && !val.isConstant()) {
            MultisetOfACnCTerms vars = this.value.get(v).getVars();
            for (ACnCTerm w : vars.elements()) {
                ACnCTerm rep = this.getRep(w);
                newcounter.put(rep, Integer.valueOf(newcounter.get(rep).intValue() - vars.numberOfOccurences(w)));
            }
        }
    }


    /** Returns the pure problems belonging to f after transforming them with the
     * quasi-solved problems and deletes the pure problem.
     */
    public List<PairOfACnCTerms> getTransformed(FunctionSymbol f) {
        List<PairOfACnCTerms> orig;
        if(this.acSig.contains(f)) {
            orig = this.acProblems.get(f);
        }
        else {
            orig = this.cProblems.get(f);
        }
        if(orig.isEmpty()) {
            return orig;
        }
        this.walkThrough(f);
        return this.getAndDeleteACnCProblems(f);
    }

    /* variables in the quasi solved problems of f are replaced by their
     * representatives */
    private void walkThrough(FunctionSymbol f) {
        if(Globals.useAssertions) {
            assert f != null;
        }
        /* quasi solved part */
        for(ACnCTerm var : this.value.keySet()) {
            ACnCTerm val = this.value.get(var);
            if(f.equals(val.getSymbol())) {
                MultisetOfACnCTerms args = val.getMultiargs();
                ArrayList<ACnCTerm> newargs = new ArrayList<ACnCTerm>();
                for (ACnCTerm elem : args.elements()) {
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
                this.value.put(var, ACnCTerm.create(f, MultisetOfACnCTerms.create(newargs), this.acSig, this.cSig));
            }
        }
    }

    /* replace variables by their representatives, apply E-Rep as long
     * as possible */
    private List<PairOfACnCTerms> getAndDeleteACnCProblems(FunctionSymbol f) {

        if(this.cSig.contains(f)) {
            /* nothing to be done for C */
            List<PairOfACnCTerms> orig = this.cProblems.get(f);
            this.cProblems.put(f, new ArrayList<PairOfACnCTerms>());
            return orig;
        }

        List<PairOfACnCTerms> orig = this.acProblems.get(f);
        this.acProblems.put(f, new ArrayList<PairOfACnCTerms>());

        List<PairOfACnCTerms> res = new ArrayList<PairOfACnCTerms>();

        for(PairOfACnCTerms p : orig) {

            ACnCTerm l = this.ERep(p.getLeft(), f);
            ACnCTerm r = this.ERep(p.getRight(), f);

            res.add(PairOfACnCTerms.create(l, r));
        }

        return res;
    }

    /* replace vars by representatives and apply ERep */
    private ACnCTerm ERep(ACnCTerm t, FunctionSymbol f) {
        if(Globals.useAssertions) {
            assert f != null;
        }
        /* replace vars by representatives */
        MultisetOfACnCTerms args = t.getMultiargs();
        ArrayList<ACnCTerm> newargs = new ArrayList<ACnCTerm>();
        for (ACnCTerm elem : args.elements()) {
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
        ArrayList<ACnCTerm> newerargs = null;
        while(changed) {
            changed = false;
            newerargs = new ArrayList<ACnCTerm>();
            for (ACnCTerm elem : newargs) {
                ACnCTerm val = this.value.get(elem);
                int n = 0;
                for(ACnCTerm elemOcc : newargs) {
                    if(elemOcc.equals(elem)) {
                        n++;
                    }
                }
                if(val!=null && f.equals(val.getSymbol())) {
                    changed = true;
                    /* add arguments */
                    MultisetOfACnCTerms valargs = val.getMultiargs();
                    for (ACnCTerm var : valargs.elements()) {
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

        return ACnCTerm.create(f, MultisetOfACnCTerms.create(newargs), this.acSig, this.cSig);
    }


    /** Transforms this problem into a substitution if it is solved.
     */
    public TRSSubstitution toSubst() {
        this.walkThrough();
        List<PairOfACnCTerms> pairs = this.Rep();

        TRSSubstitution res = TRSSubstitution.create();
        for(PairOfACnCTerms p : pairs) {
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
        for(ACnCTerm var:this.value.keySet()) {
            ACnCTerm val = this.value.get(var);
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
            FunctionSymbol f = val.getSymbol();
            if(val.hasArgs()) {
                List<ACnCTerm> args = val.getArgs();
                ArrayList<ACnCTerm> newargs = new ArrayList<ACnCTerm>();
                for(ACnCTerm arg:args) {
                    newargs.add(this.walkRec(arg));
                }
                return ACnCTerm.create(f, newargs, this.acSig, this.cSig);
            }
            else {
                MultisetOfACnCTerms args = val.getMultiargs();
                ArrayList<ACnCTerm> newargs = new ArrayList<ACnCTerm>();
                for(ACnCTerm arg:args.elements()) {
                    ACnCTerm newEl = this.walkRec(arg);
                    for(int i=0;i<args.numberOfOccurences(arg);i++) {
                        newargs.add(newEl);
                    }
                }
                return ACnCTerm.create(f, MultisetOfACnCTerms.create(newargs), this.acSig, this.cSig);
            }
        }
    }

    /* apply Rep steps as long as possible */
    private List<PairOfACnCTerms> Rep() {
        boolean changed = true;
        while(changed) {
            changed = this.repStep();
        }

        List<PairOfACnCTerms> res = new ArrayList<PairOfACnCTerms>();
        for(ACnCTerm var:this.value.keySet()) {
            res.add(PairOfACnCTerms.create(var, this.value.get(var)));
        }
        return res;
    }


    /* performs one replacement step and returns whether something was changed */
    private boolean repStep() {
        boolean res = false;

        for(ACnCTerm var:this.value.keySet()) {
            ACnCTerm val = this.value.get(var);
            res = res || this.repAll(var, val);
        }

        return res;
    }

    /* replace all occurences of var on a rhs by val */
    private boolean repAll(ACnCTerm var, ACnCTerm val) {
        boolean res = false;
        for(ACnCTerm othervar:this.value.keySet()) {
            if(!var.equals(othervar)) {
                ACnCTerm orig = this.value.get(othervar);
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

        FunctionSymbol f = orig.getSymbol();
        if(orig.hasArgs()) {
            List<ACnCTerm> args = orig.getArgs();
            ArrayList<ACnCTerm> newargs = new ArrayList<ACnCTerm>();
            for(ACnCTerm i:args) {
                newargs.add(this.repRec(var, val, i, flag));
            }
            return ACnCTerm.create(f, newargs, this.acSig, this.cSig);
        }
        else {
            MultisetOfACnCTerms args = orig.getMultiargs();
            ArrayList<ACnCTerm> newargs = new ArrayList<ACnCTerm>();
            for (ACnCTerm elem : args.elements()) {
                ACnCTerm newelem = this.repRec(var, val, elem, flag);
                if(!f.equals(newelem.getSymbol())) {
                    for(int i=0;i<args.numberOfOccurences(elem);i++) {
                        newargs.add(newelem);
                    }
                }
                else {
                    /* flatten */
                    int n = args.numberOfOccurences(elem);
                    MultisetOfACnCTerms newestargs = newelem.getMultiargs();

                    for (ACnCTerm newestelem : newestargs.elements()) {
                        for(int i=0;i<n*newestargs.numberOfOccurences(newestelem);i++) {
                            newargs.add(newestelem);
                        }
                    }
                }
            }
            return ACnCTerm.create(f, MultisetOfACnCTerms.create(newargs), this.acSig, this.cSig);
        }
    }


    /* Get the representative of the variable x */
    private ACnCTerm getRep(ACnCTerm x) {
        ACnCTerm ot = this.value.get(x);
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
    private void setValue(ACnCTerm x, ACnCTerm val) {
        ACnCTerm old = this.value.get(x);
        if(old==null && !val.isVariable()) {
            /* noting yet ==> initialize counter */
            MultisetOfACnCTerms vars = val.getVars();
            for (ACnCTerm v : vars.elements()) {
                this.incCounter(this.getRep(v), vars.numberOfOccurences(v));
            }
        }
        else if(old!=null && !old.isVariable()) {
            /* decrement for old */
            MultisetOfACnCTerms vars = old.getVars();
            for (ACnCTerm v : vars.elements()) {
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
        Integer o = this.counter.get(v);
        int res = inc;
        if(o!=null) {
            res += o.intValue();
        }
        this.counter.put(v, Integer.valueOf(res));
    }

    private void decCounter(ACnCTerm v, int dec) {
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

    private int getCounter(ACnCTerm v) {
        Integer o = this.counter.get(v);
        if(o==null) {
            return 0;
        }
        else {
            return o.intValue();
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


