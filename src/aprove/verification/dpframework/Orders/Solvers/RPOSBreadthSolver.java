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

/** New RPOS-solver, calculates all (minimal) statuses
 * that solve the constraints.
 *
 *   @author      Stephan Falke
 *   @version $Id$
 */

public class RPOSBreadthSolver implements AbortableConstraintSolver<TRSTerm>, ProvidesCriticalConstraint {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private ExtHashSetOfStatuses<FunctionSymbol> initialStatuses;
    private Poset<FunctionSymbol> finalPrecedence;
    private StatusMap<FunctionSymbol> finalStatusMap;
    private ExtHashSetOfStatuses<FunctionSymbol> allFinalStatuses;
    private Constraint<TRSTerm> crit;

    /* constructors */

    private RPOSBreadthSolver(List<FunctionSymbol> signature, ExtHashSetOfStatuses<FunctionSymbol> initialStatuses) {
        this.signature = signature;
        this.initialStatuses = initialStatuses;
        this.finalPrecedence = null;
        this.finalStatusMap = null;
        this.allFinalStatuses = null;
        this.crit = null;
    }

    /** Creates a new instance of <code>RPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     */
    public static RPOSBreadthSolver create(Set<FunctionSymbol> signature) {
        return new RPOSBreadthSolver(new ArrayList<FunctionSymbol>(signature), null);
    }

    /** Creates a new instance of <code>RPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialStatuses    the initial statuses
     */
    public static RPOSBreadthSolver create(Set<FunctionSymbol> signature,
            ExtHashSetOfStatuses<FunctionSymbol> initialStatuses) {
        return new RPOSBreadthSolver(new ArrayList<FunctionSymbol>(signature), initialStatuses);
    }

    /** Returns a final precedence, <code>null</code> if the constraints
     * couldn't be solved.
     */
    public Poset<FunctionSymbol> getFinalPrecedence() {
        return this.finalPrecedence;
    }

    /** Returns a final status map, <code>null</code> if the constraints
     * couldn't be solved.
     */
    public StatusMap<FunctionSymbol> getFinalStatusMap() {
        return this.finalStatusMap;
    }

    /** Returns all final statuses that solve the constraints,
     * <code>null</code> if no such status was found.
     */
    public ExtHashSetOfStatuses<FunctionSymbol> getAllFinalStatuses() {
        return this.allFinalStatuses;
    }

    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            return RPOS.create(this.finalPrecedence, this.finalStatusMap);
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
            return RPOS.create(this.finalPrecedence, this.finalStatusMap);
        }
        else {
            return null;
        }
    }

    /* return 'true' if the rules are ordered by the lexicographic path order
     * with status, return 'false' otherwise.
     * The lexicographic path order with status is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       there exists an 1<=i<=n such that
     *                       s_p(1) = t_p(1), ... ,s_p(i-1)=t_p(i-1),
     *                       s_p(i)>t_p(i) and s>t_p(j) for all i<j<=n, if
     *                       f has permutation p as status
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     *                   or
     *                  (2d) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       {s_1, ... , s_n} >> {t_1, ... , t_n}
     *                       where >> is the multiset extension, if
     *                       f has multiset status
     * Terms are considered equal their multiterms according to the status map
     * are equal.
     * | is an partial order of the function symbols and is generated
     * 'on the fly' with this implementation.
     * p is a fixed permutation, for every n-ary f, of {1,...,n} which is
     * also generated 'on the fly'.
     */
    private boolean tryToOrder() {
        boolean result = true;
        this.finalPrecedence = null;
        this.finalStatusMap = null;
        this.allFinalStatuses = null;

        /* commonStat will contain the intersection of the statuses that
         * solve the constraints considered so far, i.e. the relations in
         * commonStat will have to be used in any case
         */
        Status<FunctionSymbol> commonStat;
        ExtHashSetOfStatuses<FunctionSymbol> allStats;

        if(this.initialStatuses==null) {
            allStats = ExtHashSetOfStatuses.create(this.signature);
            commonStat = Status.create(this.signature);
            allStats.add(commonStat);
        }
        else {
            try {
                allStats = this.initialStatuses.deepcopy();
                commonStat = allStats.intersectAll();
            }
            catch(StatusException e) {
                allStats = ExtHashSetOfStatuses.create(this.signature);
                commonStat = Status.create(this.signature);
                allStats.add(commonStat);
            }
        }

        Iterator<Constraint<TRSTerm>> i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfStatuses<FunctionSymbol> newStats;
        while(i.hasNext() && result==true) {
            c = i.next();
            try {
                newStats = this.RPOS(c, commonStat);
                /* newStats contains the extensions of commonStat that solve c */
                if(newStats.size()==0) {
                    /* this constraint can't be oriented */
                    this.crit = c;
                    result = false;
                }
                else {
                    allStats = allStats.mergeAll(newStats).minimalElements();
                    /* allStats are the minimal precedences that solve all
                     * constraints considered so far
                     */
                    if(allStats.size()==0) {
                        this.crit = c;
                        result = false;
                    }
                    else {
                        commonStat = allStats.intersectAll();
                    }
                }
            }
            catch (StatusException excp) {
                this.crit = c;
                result = false;
            }
        }

        if(result==true) {
            Iterator<Status<FunctionSymbol>> j = allStats.iterator();
            if(j.hasNext()) {
                /* just take an arbitrary status */
                Status<FunctionSymbol> finalStatus = j.next();
                this.finalPrecedence = finalStatus.getPrecedence();
                this.finalStatusMap = finalStatus.getStatusMap();
            }
            this.allFinalStatuses = allStats;
        }

        return result;
    }

    private boolean verboseTryToOrder() {
        boolean result = true;
        this.finalPrecedence = null;
        this.finalStatusMap = null;
        this.allFinalStatuses = null;

        /* commonStat will contain the intersection of the statuses that
         * solve the constraints considered so far, i.e. the relations in
         * commonStat will have to be used in any case
         */
        Status<FunctionSymbol> commonStat;
        ExtHashSetOfStatuses<FunctionSymbol> allStats;

        if(this.initialStatuses==null) {
            allStats = ExtHashSetOfStatuses.create(this.signature);
            commonStat = Status.create(this.signature);
            allStats.add(commonStat);
        }
        else {
            try {
                allStats = this.initialStatuses.deepcopy();
                commonStat = allStats.intersectAll();
            }
            catch(StatusException e) {
                allStats = ExtHashSetOfStatuses.create(this.signature);
                commonStat = Status.create(this.signature);
                allStats.add(commonStat);
            }
        }

        Iterator<Constraint<TRSTerm>> i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfStatuses<FunctionSymbol> newStats;
        while(i.hasNext() && result==true) {
            c = i.next();
            try {
                //System.out.print(c + ": ");

                newStats = this.RPOS(c, commonStat);
                /* newStats contains the extensions of commonStat that solve c */
                if(newStats.size()==0) {
                    if(this.RPOS(c, Status.create(Poset.create(this.signature),
                            StatusMap.create(this.signature))).size()==0) {
                        //System.out.println("Not satisfiable by any RPOS!");
                    }
                    else {
                        //System.out.println("No extension found!");
                    }
                    /* this constraint can't be oriented */
                    this.crit = c;
                    result = false;
                }
                else {
                    allStats = allStats.mergeAll(newStats).minimalElements();
                    /* allStats are the minimal precedences that solve all
                     * constraints considered so far
                     */
                    if(allStats.size()==0) {
                        //System.out.println("No extension found!");
                        this.crit = c;
                        result = false;
                    }
                    else {
                        //System.out.println("OK");
                        commonStat = allStats.intersectAll();
                    }
                }
            }
            catch (StatusException excp) {
                this.crit = c;
                result = false;
            }
        }

        if(result==true) {
            Iterator<Status<FunctionSymbol>> j = allStats.iterator();
            if(j.hasNext()) {
                /* just take an arbitrary status */
                Status<FunctionSymbol> finalStatus = j.next();
                this.finalPrecedence = finalStatus.getPrecedence();
                this.finalStatusMap = finalStatus.getStatusMap();
            }
            this.allFinalStatuses = allStats;
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
    private ExtHashSetOfStatuses<FunctionSymbol> RPOS(Constraint<TRSTerm> c, Status<FunctionSymbol> stat) throws StatusException {
        //    AProVETime.checkTimer();
        TRSTerm origL = c.getLeft();
        TRSTerm origR = c.getRight();
        ExtHashSetOfStatuses<FunctionSymbol> res = ExtHashSetOfStatuses.create(this.signature);
        Status<FunctionSymbol> newStat;

        RPOS rpos = RPOS.create(stat.getPrecedence(),
                stat.getStatusMap());
        if(rpos.solves(c)) {
            /* the current status suffices */
            res.add(stat);
            return res;
        }
        if(rpos.inRelation(origR, origL)) {
            /* it won't work */
            return res;
        }

        if(Multiterm.create(origL, stat.getStatusMap()).equals(Multiterm.create(origR, stat.getStatusMap()))) {
            /* (1) is not true -> check for strictness */
            if (c.getType()==OrderRelation.GR) {
                /* it won't work, so return empty set of statuses */
                return res;
            }
            else {
                /* the current status suffices */
                res.add(stat);
                return res;
            }
        }

        if(c.getType()==OrderRelation.EQ) {
            return RPOS.minimalEqualizers(origL, origR, stat).minimalElements();
        }

        if(origL.isVariable()) {
            if(!origR.isVariable() && c.getType()==OrderRelation.GE) {
                TRSFunctionApplication r = (TRSFunctionApplication)origR;
                FunctionSymbol rSymb = r.getRootSymbol();
                if(rSymb.getArity()==0) {
                    /* minimal constants are GE to variables */
                    newStat = stat.deepcopy();
                    boolean OK;
                    try {
                        newStat.setMinimal(rSymb);
                        OK = true;
                    }
                    catch(StatusException e) {
                        /* that didn't work... */
                        OK = false;
                    }
                    if(OK) {
                        res.add(newStat);
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
                /* the current status suffices */
                res.add(stat);
                return res;
            }
            else {
                /* it won't work, so return empty set of statuses */
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
                res = res.union(this.RPOS(Constraint.create(l.getArgument(0),
                        r.getArgument(0),
                        OrderRelation.GR),
                        stat));
                if(c.getType()==OrderRelation.GE) {
                    res=res.union(RPOS.minimalGENGRs(l, r, stat)).minimalElements();
                }
                return res.minimalElements();
            }

            if(stat.hasMultisetStatus(symbLeft)) {
                MultiSet<TRSTerm> argL = new HashMultiSet<TRSTerm>(l.getArguments());
                MultiSet<TRSTerm> argR = new HashMultiSet<TRSTerm>(r.getArguments());
                MultisetExtension mul = MultisetExtension.create(rpos);

                OrderRelation tmpRes = mul.relate(argL, argR);
                if(tmpRes==OrderRelation.GR) {
                    /* current precedence suffices */
                    res.add(stat);
                    return res;
                }
                else {
                    MultiSet<TRSTerm> L = mul.getLeft();
                    MultiSet<TRSTerm> R = mul.getRight();

                    List<TRSTerm> LVector = L.toList();
                    List<TRSTerm> RVector = R.toList();

                    int sizeL = LVector.size();
                    int sizeR = RVector.size();

                    DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfStatuses<FunctionSymbol>> dh = DoubleHash.create();
                    Iterator<TRSTerm> le = LVector.iterator();
                    Iterator<TRSTerm> re;

                    while(le.hasNext()) {
                        re = RVector.iterator();
                        newLeft = (TRSTerm)le.next();
                        while(re.hasNext()) {
                            newRight = (TRSTerm)re.next();
                            dh.put(newLeft, newRight,
                                    this.RPOS(Constraint.create(newLeft, newRight, OrderRelation.GE),
                                            stat));
                        }
                    }

                    int i;
                    ExtHashSetOfStatuses<FunctionSymbol> newRes;
                    ExtHashSetOfStatuses<FunctionSymbol> finalRes;
                    Status<FunctionSymbol> testStat;
                    for (Sequence s : SequenceGenerator.create(sizeR, sizeL)) {
                        //    AProVETime.checkTimer();
                        newStat = stat.deepcopy();
                        newRes = ExtHashSetOfStatuses.create(this.signature);
                        newRes.add(newStat);
                        i = 0;
                        while(i < sizeR && !newRes.isEmpty()) {
                            newLeft = LVector.get(s.get(i));
                            newRight = RVector.get(i);
                            newRes = newRes.mergeAll(dh.get(newLeft, newRight)).minimalElements();
                            i++;
                        }
                        if(!newRes.isEmpty()) {
                            /* maybe we did too much, i.e. the terms a equal */
                            finalRes = ExtHashSetOfStatuses.create(this.signature);
                            Iterator<Status<FunctionSymbol>> j = newRes.iterator();
                            while(j.hasNext()) {
                                testStat = j.next();
                                mul = MultisetExtension.create(RPOS.create(
                                        testStat.getPrecedence(),
                                        testStat.getStatusMap()));
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
                    res=res.union(RPOS.minimalGENGRs(l, r, stat)).minimalElements();
                }

                return res.minimalElements();
            }

            else if(stat.hasPermutation(symbLeft)) {
                /* use the given permutation */
                DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfStatuses<FunctionSymbol>> equalizers = DoubleHash.create();
                DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfStatuses<FunctionSymbol>> dh = DoubleHash.create();
                ExtHashSetOfStatuses<FunctionSymbol> newRes;
                Permutation p = stat.getPermutation(symbLeft);
                int n = ((FunctionSymbol)symbLeft).getArity();
                TRSFunctionApplication permL = LPOS.permuteTerm(l, p);
                TRSFunctionApplication permR = LPOS.permuteTerm(r, p);

                e1 = permL.getArguments().iterator();
                e2 = permR.getArguments().iterator();

                while(e1.hasNext()) {
                    newLeft = (TRSTerm)e1.next();
                    newRight = (TRSTerm)e2.next();
                    equalizers.put(newLeft, newRight,
                            RPOS.minimalGENGRs(newLeft, newRight, stat));
                    dh.put(newLeft, newRight, this.RPOS(Constraint.create(newLeft, newRight, OrderRelation.GR),
                            stat));
                    dh.put(l, newRight, this.RPOS(Constraint.create(l, newRight, OrderRelation.GR),
                            stat));
                }

                for(int i=0; i<n; i++) {
                    newStat = stat.deepcopy();
                    newRes = ExtHashSetOfStatuses.create(this.signature);
                    newRes.add(newStat);
                    int j=0;
                    while(j < i && !newRes.isEmpty()) {
                        newLeft = permL.getArgument(j);
                        newRight = permR.getArgument(j);
                        newRes = newRes.mergeAll(equalizers.get(newLeft, newRight)).minimalElements();
                        j++;
                    }
                    if(!newRes.isEmpty()) {
                        newLeft = permL.getArgument(i);
                        newRight = permR.getArgument(i);
                        newRes = newRes.mergeAll(dh.get(newLeft, newRight)).minimalElements();
                    }
                    j=i+1;
                    while(j < n && !newRes.isEmpty()) {
                        newRight = permR.getArgument(j);
                        newRes = newRes.mergeAll(dh.get(l, newRight)).minimalElements();
                        j++;
                    }

                    if(!newRes.isEmpty()) {
                        res = res.union(newRes);
                    }
                }

                /* and don't forget (2a)! */
                e1 = l.getArguments().iterator();
                while(e1.hasNext()) {
                    newLeft = (TRSTerm) e1.next();
                    res = res.union(this.RPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
                }

                if(c.getType()==OrderRelation.GE) {
                    res=res.union(RPOS.minimalGENGRs(l, r, stat)).minimalElements();
                }

                return res.minimalElements();
            }

            else {
                /* try all permutations and multiset status*/
                int n = ((FunctionSymbol) symbLeft).getArity();
                Iterable<Permutation> perm = PermutationGenerator.create(n);
                TRSTerm permL;
                TRSTerm permR;
                ExtHashSetOfStatuses<FunctionSymbol> newRes;
                DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfStatuses<FunctionSymbol>> dh = DoubleHash.create();
                DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfStatuses<FunctionSymbol>> equalizers = DoubleHash.create();

                e1 = l.getArguments().iterator();
                e2 = r.getArguments().iterator();
                while(e1.hasNext()) {
                    /* compare corresponding subterms l_i, r_i and
                     * also compare l to r_i
                     */
                    newLeft = (TRSTerm) e1.next();
                    newRight = (TRSTerm) e2.next();
                    dh.put(newLeft, newRight,
                            this.RPOS(Constraint.create(newLeft, newRight, OrderRelation.GR),
                                    stat));
                    dh.put(l, newRight,
                            this.RPOS(Constraint.create(l, newRight, OrderRelation.GR),
                                    stat));
                    equalizers.put(newLeft, newRight,
                            RPOS.minimalGENGRs(newLeft, newRight, stat));
                }

                for (Permutation p : perm) {
                    newStat = stat.deepcopy();
                    newStat.assignPermutation(symbLeft, p);

                    permL = LPOS.permuteTerm(l, p);
                    permR = LPOS.permuteTerm(r, p);

                    for(int i=0; i<n; i++) {
                        newRes = ExtHashSetOfStatuses.create(this.signature);
                        newRes.add(newStat.deepcopy());
                        int j=0;
                        while(j < i && !newRes.isEmpty()) {
                            newLeft = ((TRSFunctionApplication)permL).getArgument(j);
                            newRight = ((TRSFunctionApplication)permR).getArgument(j);
                            newRes = newRes.mergeAll(equalizers.get(newLeft, newRight)).minimalElements();
                            j++;
                        }
                        if(!newRes.isEmpty()) {
                            newLeft = ((TRSFunctionApplication)permL).getArgument(i);
                            newRight = ((TRSFunctionApplication)permR).getArgument(i);
                            newRes = newRes.mergeAll(dh.get(newLeft, newRight)).minimalElements();
                        }
                        j=i+1;
                        while(j < n && !newRes.isEmpty()) {
                            newRight = ((TRSFunctionApplication)permR).getArgument(j);
                            newRes = newRes.mergeAll(dh.get(l, newRight)).minimalElements();
                            j++;
                        }

                        if(!newRes.isEmpty()) {
                            res = res.union(newRes);
                        }
                    }
                }

                /* multiset status */
                newStat = stat.deepcopy();
                newStat.assignMultisetStatus(symbLeft);
                res = res.union(this.RPOS(c, newStat));

                /* and don't forget (2a)! */
                e1 = l.getArguments().iterator();

                while(e1.hasNext()) {
                    newLeft = (TRSTerm) e1.next();
                    res = res.union(this.RPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
                }

                if(c.getType()==OrderRelation.GE) {
                    res=res.union(RPOS.minimalGENGRs(l, r, stat)).minimalElements();
                }

                return res.minimalElements();
            }
        }
        else if(stat.isGreater(symbLeft, symbRight)) {
            /* (2c), no need for (2a) */

            e2 = r.getArguments().iterator();

            newStat = stat.deepcopy();
            res.add(newStat);
            while(e2.hasNext() && !res.isEmpty()) {
                newRight = (TRSTerm) e2.next();
                res = res.mergeAll(this.RPOS(Constraint.create(l, newRight, OrderRelation.GR), newStat)).minimalElements();
                newStat = res.intersectAll();
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(RPOS.minimalGENGRs(l, r, stat)).minimalElements();
            }

            return res.minimalElements();
        }

        else if(stat.isGreater(symbRight, symbLeft)) {
            /* try (2a) */
            e1 = l.getArguments().iterator();

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.RPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(RPOS.minimalGENGRs(l, r, stat)).minimalElements();
            }

            return res.minimalElements();
        }

        else {
            /* symbRightName and symbLeftName are incomparable */

            /* enrich the precedence by symbLeftName | symbRightName */
            newStat = stat.deepcopy();
            newStat.setGreater(symbLeft, symbRight);

            res = this.RPOS(c, newStat);

            /* and don't forget (2a)! */
            e1 = l.getArguments().iterator();

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.RPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(RPOS.minimalGENGRs(l, r, stat)).minimalElements();
            }

            return res.minimalElements();
        }
    }

}
