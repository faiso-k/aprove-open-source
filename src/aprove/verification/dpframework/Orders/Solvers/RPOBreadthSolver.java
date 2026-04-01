package aprove.verification.dpframework.Orders.Solvers ;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.DoubleHash;
import aprove.verification.dpframework.Orders.Utility.Multiterm;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** New RPO-solver, calcultes all (minimal) precedences
 * that solve the constraints.
 *
 *   @author      Stephan Falke
 *   @version $Id$
 */

public class RPOBreadthSolver implements AbortableConstraintSolver<TRSTerm>, ProvidesCriticalConstraint<TRSTerm> {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private ExtHashSetOfPosets<FunctionSymbol> initialPrecedences;
    private Poset<FunctionSymbol> finalPrecedence;
    private ExtHashSetOfPosets<FunctionSymbol> allFinalPrecedences;
    private Constraint<TRSTerm> crit;

    /* constructors */

    private RPOBreadthSolver(List<FunctionSymbol> signature, ExtHashSetOfPosets<FunctionSymbol> initialPrecedences) {
        this.signature = signature;
        this.initialPrecedences = initialPrecedences;
        this.finalPrecedence = null;
        this.allFinalPrecedences = null;
        this.crit = null;
    }

    /** Creates a new instance of <code>RPOBreadthSolver</code>.
     * @param signature   the names of the symbols
     */
    public static RPOBreadthSolver create(Set<FunctionSymbol> signature) {
        return new RPOBreadthSolver(new ArrayList<FunctionSymbol>(signature), null);
    }

    /** Creates a new instance of <code>RPOBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedences   the initial precedences
     */
    public static RPOBreadthSolver create(Set<FunctionSymbol> signature,
            ExtHashSetOfPosets<FunctionSymbol> initialPrecedences) {
        return new RPOBreadthSolver(new ArrayList<FunctionSymbol>(signature),
                initialPrecedences);
    }

    /** Returns a final precedence, <code>null</code> if the constraints
     * couldn't be solved.
     */
    public Poset<FunctionSymbol> getFinalPrecedence() {
        return this.finalPrecedence;
    }

    /** Returns all final precedences that solve the constraints,
     * <code>null</code> if no such precedence was found.
     */
    public ExtHashSetOfPosets<FunctionSymbol> getAllFinalPrecedences() {
        return this.allFinalPrecedences;
    }

    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            return RPO.create(this.finalPrecedence);
        }
        else {
            return null;
        }
    }

    /** Verbose version of <code>solve</code>.
     * @see #solve(Set<Constraint>)
     */
    public ExportableOrder<TRSTerm> verboseSolve(Set<Constraint<TRSTerm>> cs) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.verboseTryToOrder()) {
            return RPO.create(this.finalPrecedence);
        }
        else {
            return null;
        }
    }

    /* return 'true' if the rules are ordered by the lexicographic path order,
     * return 'false' otherwise.
     * The recursive path order is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       {s_1, ... , s_n} >> {t_1, ... , t_n}
     *                       where >> is the multiset extension
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     * Terms are considered equal if they differ only in a permutation of
     * their arguments.
     * | is an partial order of the function symbols and is generated
     * 'on the fly' with this implementation.
     */
    private boolean tryToOrder() {
        boolean result = true;
        this.finalPrecedence = null;
        this.allFinalPrecedences = null;

        /* commonPrec will contain the intersection of the precedences that
         * solve the constraints considered so far, i.e. the relations in
         * commonPrec will have to be used in any case
         */
        Poset<FunctionSymbol> commonPrec;
        ExtHashSetOfPosets<FunctionSymbol> allPrecs;

        if(this.initialPrecedences==null) {
            allPrecs = ExtHashSetOfPosets.create(this.signature);
            commonPrec = Poset.create(this.signature);
            allPrecs.add(commonPrec);
        }
        else {
            try {
                allPrecs = this.initialPrecedences.deepcopy();
                commonPrec = allPrecs.intersectAll();
            }
            catch(PosetException e) {
                allPrecs = ExtHashSetOfPosets.create(this.signature);
                commonPrec = Poset.create(this.signature);
                allPrecs.add(commonPrec);
            }
        }

        Iterator<Constraint<TRSTerm>> i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfPosets<FunctionSymbol> newPrecs;
        while(i.hasNext() && result==true) {
            c = i.next();
            try {
                newPrecs = this.RPO(c, commonPrec);
                /* newPrecs contains the extensions of commonPrec that solve c */
                if(newPrecs.size()==0) {
                    /* this constraint can't be oriented */
                    this.crit = c;
                    result = false;
                }
                else {
                    allPrecs = allPrecs.mergeAll(newPrecs).minimalElements();
                    /* allPrecs are the minimal precedences that solve all
                     * constraints considered so far
                     */
                    if(allPrecs.size()==0) {
                        this.crit = c;
                        result = false;
                    }
                    else {
                        commonPrec = allPrecs.intersectAll();
                    }
                }
            }
            catch (OrderedSetException excp) {
                this.crit = c;
                result = false;
            }
        }

        if(result==true) {
            Iterator<Poset<FunctionSymbol>> ips = allPrecs.iterator();
            if(ips.hasNext()) {
                /* just take an arbitrary precedence */
                this.finalPrecedence = ips.next();
            }
            this.allFinalPrecedences = allPrecs;
        }

        return result;
    }

    private boolean verboseTryToOrder() {
        boolean result = true;
        this.finalPrecedence = null;
        this.allFinalPrecedences = null;

        /* commonPrec will contain the intersection of the precedences that
         * solve the constraints considered so far, i.e. the relations in
         * commonPrec will have to be used in any case
         */
        Poset<FunctionSymbol> commonPrec;
        ExtHashSetOfPosets<FunctionSymbol> allPrecs;

        if(this.initialPrecedences==null) {
            allPrecs = ExtHashSetOfPosets.create(this.signature);
            commonPrec = Poset.create(this.signature);
            allPrecs.add(commonPrec);
        }
        else {
            try {
                allPrecs = this.initialPrecedences.deepcopy();
                commonPrec = allPrecs.intersectAll();
            }
            catch(PosetException e) {
                allPrecs = ExtHashSetOfPosets.create(this.signature);
                commonPrec = Poset.create(this.signature);
                allPrecs.add(commonPrec);
            }
        }

        Iterator<Constraint<TRSTerm>> i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfPosets<FunctionSymbol> newPrecs;
        while(i.hasNext() && result==true) {
            c = i.next();
            try {
                //System.out.print(c + ": ");

                newPrecs = this.RPO(c, commonPrec);
                /* newPrecs contains the extensions of commonPrec that solve c */
                if(newPrecs.size()==0) {
                    if(this.RPO(c, Poset.create(this.signature)).size()==0) {
                        //System.out.println("Not satisfiable by any RPO!");
                    }
                    else {
                        //System.out.println("No extension found!");
                    }
                    /* this constraint can't be oriented */
                    this.crit = c;
                    result = false;
                }
                else {
                    allPrecs = allPrecs.mergeAll(newPrecs).minimalElements();
                    /* allPrecs are the minimal precedences that solve all
                     * constraints considered so far
                     */
                    if(allPrecs.size()==0) {
                        //System.out.println("No extension found!");
                        this.crit = c;
                        result = false;
                    }
                    else {
                        //System.out.println("OK");
                        commonPrec = allPrecs.intersectAll();
                    }
                }
            }
            catch (OrderedSetException excp) {
                this.crit = c;
                result = false;
            }
        }

        if(result==true) {
            Iterator<Poset<FunctionSymbol>> ips = allPrecs.iterator();
            if(ips.hasNext()) {
                /* just take an arbitrary precedence */
                this.finalPrecedence = ips.next();
            }
            this.allFinalPrecedences = allPrecs;
        }

        return result;
    }

    /** Returns the first constraint that could not be satisfied.
     */
    @Override
    public Constraint<TRSTerm> getCriticalConstraint() {
        return this.crit;
    }

    /* returns the extensions of prec that solve c */
    private ExtHashSetOfPosets<FunctionSymbol> RPO(Constraint<TRSTerm> c, Poset<FunctionSymbol> prec) throws OrderedSetException {
        //    AProVETime.checkTimer();
        TRSTerm origL = c.getLeft();
        TRSTerm origR = c.getRight();
        ExtHashSetOfPosets<FunctionSymbol> res = ExtHashSetOfPosets.create(this.signature);
        Poset<FunctionSymbol> newPrec;

        RPO rpo = RPO.create(prec);
        if(rpo.solves(c)) {
            /* the current precedence suffices */
            res.add(prec);
            return res;
        }
        if(rpo.inRelation(origR, origL)) {
            /* it won't work */
            return res;
        }

        if(Multiterm.create(origL).equals(Multiterm.create(origR))) {
            /* (1) is not true -> check for strictness */
            if (c.getType()==OrderRelation.GR) {
                /* it won't work, so return empty set of posets */
                return res;
            }
            else {
                /* the current precedence suffices */
                res.add(prec);
                return res;
            }
        }

        if(c.getType()==OrderRelation.EQ) {
            /* nope! */
            return res;
        }

        if(origL.isVariable()) {
            if(!origR.isVariable() && c.getType()==OrderRelation.GE) {
                TRSFunctionApplication r = (TRSFunctionApplication)origR;
                FunctionSymbol rSymb = r.getRootSymbol();
                if(rSymb.getArity()==0) {
                    /* minimal constants are GE to variables */
                    newPrec = prec.deepcopy();
                    boolean OK;
                    try {
                        newPrec.setMinimal(rSymb);
                        OK = true;
                    }
                    catch(PosetException e) {
                        /* that didn't work... */
                        OK = false;
                    }
                    if(OK) {
                        res.add(newPrec);
                        return res;
                    }
                    else {
                        /* empty */
                        return res;
                    }
                }
                else {
                    /* empty */
                    return res;
                }
            }
            else {
                /* empty */
                return res;
            }
        }

        TRSFunctionApplication l = (TRSFunctionApplication)origL;
        /* l = f(l_1, ..., l_n) */

        if(origR.isVariable()) {
            if(l.getVariables().contains(origR)) {
                /* the current precedence suffices */
                res.add(prec);
                return res;
            }
            else {
                /* it won't work, so return empty set of posets */
                return res;
            }
        }

        TRSFunctionApplication r = (TRSFunctionApplication)origR;
        /* r = g(r_1, ..., r_m) */
        Iterator e1;
        Iterator e2;
        FunctionSymbol symbLeft = l.getRootSymbol();
        FunctionSymbol symbRight = r.getRootSymbol();
        TRSTerm newLeft;
        TRSTerm newRight;

        if(symbLeft.equals(symbRight)) {
            if(((FunctionSymbol)symbLeft).getArity()==1) {
                res = res.union(this.RPO(Constraint.create(l.getArgument(0),
                        r.getArgument(0),
                        OrderRelation.GR),
                        prec));

                if(c.getType()==OrderRelation.GE) {
                    res=res.union(RPO.minimalGENGRs(l, r, prec));
                }

                return res.minimalElements();
            }

            /* this case must be handeled by (2b) */
            MultiSet<TRSTerm> argL = new HashMultiSet<TRSTerm>(l.getArguments());
            MultiSet<TRSTerm> argR = new HashMultiSet<TRSTerm>(r.getArguments());
            MultisetExtension mul = MultisetExtension.create(rpo);

            OrderRelation tmpRes = mul.relate(argL, argR);
            if(tmpRes==OrderRelation.GR) {
                /* current precedence suffices */
                res.add(prec);
                return res;
            }
            else {
                MultiSet<TRSTerm> L = mul.getLeft();
                MultiSet<TRSTerm> R = mul.getRight();

                List<TRSTerm> LVector = L.toList();
                List<TRSTerm> RVector = R.toList();

                int sizeL = LVector.size();
                int sizeR = RVector.size();

                DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfPosets<FunctionSymbol>> dh = DoubleHash.create();
                Iterator<TRSTerm> le = LVector.iterator();
                Iterator<TRSTerm> re;

                while(le.hasNext()) {
                    re = RVector.iterator();
                    newLeft = le.next();
                    while(re.hasNext()) {
                        newRight = re.next();
                        dh.put(newLeft, newRight,
                                this.RPO(Constraint.create(newLeft, newRight, OrderRelation.GE),
                                        prec));
                    }
                }

                int i;
                ExtHashSetOfPosets<FunctionSymbol> newRes;
                ExtHashSetOfPosets<FunctionSymbol> finalRes;
                for (Sequence s : SequenceGenerator.create(sizeR, sizeL)) {
                    //    AProVETime.checkTimer();
                    newPrec = prec.deepcopy();
                    newRes = ExtHashSetOfPosets.create(this.signature);
                    newRes.add(newPrec);
                    i = 0;
                    while(i < sizeR && !newRes.isEmpty()) {
                        newLeft = LVector.get(s.get(i));
                        newRight = RVector.get(i);
                        newRes = newRes.mergeAll(dh.get(newLeft, newRight)).minimalElements();
                        i++;
                    }
                    if(!newRes.isEmpty()) {
                        /* maybe we did too much, i.e. the terms a equal */
                        finalRes = ExtHashSetOfPosets.create(this.signature);
                        Iterator<Poset<FunctionSymbol>> j = newRes.iterator();
                        while(j.hasNext()) {
                            Poset<FunctionSymbol> testStat = j.next();
                            mul = MultisetExtension.create(RPO.create(testStat));
                            if(mul.relate(argL, argR)==OrderRelation.GR) {
                                finalRes.add(testStat);
                            }
                        }
                        if(!finalRes.isEmpty()) {
                            res = res.union(finalRes);
                        }
                    }
                }
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(RPO.minimalGENGRs(l, r, prec));
            }

            return res.minimalElements();
        }

        else if(prec.isGreater(symbLeft, symbRight)) {
            /* (2c), no need for (2a) */

            e2 = r.getArguments().iterator();

            newPrec = prec.deepcopy();
            res.add(newPrec);
            while(e2.hasNext() && !res.isEmpty()) {
                newRight = (TRSTerm) e2.next();
                res = res.mergeAll(this.RPO(Constraint.create(l, newRight, OrderRelation.GR), newPrec)).minimalElements();
                newPrec = res.intersectAll();
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(RPO.minimalGENGRs(l, r, prec));
            }

            return res.minimalElements();
        }

        else if(prec.isGreater(symbRight, symbLeft)) {
            /* try non strict (2a) */
            e1 = l.getArguments().iterator();

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.RPO(Constraint.create(newLeft, r, OrderRelation.GE), prec));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(RPO.minimalGENGRs(l, r, prec));
            }

            return res.minimalElements();
        }

        else {
            /* symbRightName and symbLeftName are incomparable */

            /* enrich the precedence by symbLeftNamy | symbRightName */
            newPrec = prec.deepcopy();
            newPrec.setGreater(symbLeft, symbRight);

            res = this.RPO(c, newPrec);

            /* and don't forget non strict (2a)! */
            e1 = l.getArguments().iterator();

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.RPO(Constraint.create(newLeft, r, OrderRelation.GE), prec));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(RPO.minimalGENGRs(l, r, prec));
            }

            return res.minimalElements();
        }
    }

}
