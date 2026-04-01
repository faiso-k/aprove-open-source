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

/** New QRPOS-solver, calculates all (minimal) statuses
 * that solve the constraints.
 *
 *   @author      Stephan Falke
 *   @version $Id$
 */

public class QRPOSBreadthSolver implements AbortableConstraintSolver<TRSTerm>, ProvidesCriticalConstraint {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private Qoset<FunctionSymbol> finalPrecedence;
    private ExtHashSetOfQuasiStatuses<FunctionSymbol> initialStatuses;
    private StatusMap<FunctionSymbol> finalStatusMap;
    private ExtHashSetOfQuasiStatuses<FunctionSymbol> allFinalStatuses;
    private Constraint<TRSTerm> crit;
    private Collection<Doubleton<FunctionSymbol>> equiv;


    /* constructors */

    private QRPOSBreadthSolver(List<FunctionSymbol> signature, ExtHashSetOfQuasiStatuses<FunctionSymbol> initialStatuses, Collection<Doubleton<FunctionSymbol>> equiv) {
        this.signature = signature;
        this.initialStatuses = initialStatuses;
        this.equiv = equiv;
        this.finalPrecedence = null;
        this.finalStatusMap = null;
        this.allFinalStatuses = null;
        this.crit = null;
    }

    /** Creates a new instance of <code>QRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     */
    public static QRPOSBreadthSolver create(Set<FunctionSymbol> signature) {
        return new QRPOSBreadthSolver(new ArrayList<FunctionSymbol>(signature), null, null);
    }

    /** Creates a new instance of <code>QRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialStatuses    the initial statuses
     */
    public static QRPOSBreadthSolver create(Set<FunctionSymbol> signature,
            ExtHashSetOfQuasiStatuses<FunctionSymbol> initialStatuses) {
        return new QRPOSBreadthSolver(new ArrayList<FunctionSymbol>(signature), initialStatuses, null);
    }

    /** Creates a new instance of <code>QRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QRPOSBreadthSolver create(Set<FunctionSymbol> signature, Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QRPOSBreadthSolver(new ArrayList<FunctionSymbol>(signature), null, equiv);
    }

    /** Creates a new instance of <code>QRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialStatuses    the initial statuses
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QRPOSBreadthSolver create(Set<FunctionSymbol> signature,
            ExtHashSetOfQuasiStatuses<FunctionSymbol> initialStatuses,
            Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QRPOSBreadthSolver(new ArrayList<FunctionSymbol>(signature), initialStatuses, equiv);
    }

    /** Returns a final precedence, <code>null</code> if the constraints
     * couldn't be solved.
     */
    public Qoset getFinalPrecedence() {
        return this.finalPrecedence;
    }

    /** Returns a final status map, <code>null</code> if the constraints
     * couldn't be solved.
     */
    public StatusMap getFinalStatusMap() {
        return this.finalStatusMap;
    }

    /** Returns all final statuses that solve the constraints,
     * <code>null</code> if no such status was found.
     */
    public ExtHashSetOfQuasiStatuses getAllFinalStatuses() {
        return this.allFinalStatuses;
    }

    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            Qoset<FunctionSymbol> p = this.finalPrecedence.deepcopy();
            try {
                p.fix();
                return QRPOS.create(p, this.finalStatusMap);
            }
            catch(OrderedSetException e) {
                return null;
            }
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
            return QRPOS.create(this.finalPrecedence, this.finalStatusMap);
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
     *                  (2b) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_n) and
     *                       there exists an 1<=i<=n such that
     *                       s_p(1) = t_p(1), ... ,s_p(i-1)=t_p(i-1),
     *                       s_p(i)>t_p(i) and s>t_p(j) for all i<j<=n, if
     *                       f has permutation p as status and f is
     *                       equivalent to g
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     *                  (2d) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m) and
     *                       {s_1, ... , s_n} >> {t_1, ... , t_m}
     *                       where >> is the multiset extension, if
     *                       f has multiset status and f is equivalent to g
     * | is an partial order of the function symbols and is generated
     * 'on the fly' with this implementation, as are the equivalences.
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
        QuasiStatus<FunctionSymbol> commonStat;
        ExtHashSetOfQuasiStatuses<FunctionSymbol> allStats;

        if(this.initialStatuses==null) {
            allStats = ExtHashSetOfQuasiStatuses.create(this.signature);
            commonStat = QuasiStatus.create(this.signature);
            allStats.add(commonStat);
        }
        else {
            try {
                allStats = this.initialStatuses.deepcopy();
                commonStat = allStats.intersectAll();
            }
            catch(QuasiStatusException e) {
                allStats = ExtHashSetOfQuasiStatuses.create(this.signature);
                commonStat = QuasiStatus.create(this.signature);
                allStats.add(commonStat);
            }
        }

        Iterator<Constraint<TRSTerm>> i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfQuasiStatuses<FunctionSymbol> newStats;
        while(i.hasNext() && result==true) {
            c = i.next();
            try {
                newStats = this.QRPOS(c, commonStat);
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
            catch (QuasiStatusException excp) {
                this.crit = c;
                result = false;
            }
        }

        if(result==true) {
            Iterator<QuasiStatus<FunctionSymbol>> j = allStats.iterator();
            if(j.hasNext()) {
                /* just take an arbitrary status */
                QuasiStatus<FunctionSymbol> finalStatus = j.next();
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
        QuasiStatus<FunctionSymbol> commonStat;
        ExtHashSetOfQuasiStatuses<FunctionSymbol> allStats;

        if(this.initialStatuses==null) {
            allStats = ExtHashSetOfQuasiStatuses.create(this.signature);
            commonStat = QuasiStatus.create(this.signature);
            allStats.add(commonStat);
        }
        else {
            try {
                allStats = this.initialStatuses.deepcopy();
                commonStat = allStats.intersectAll();
            }
            catch(QuasiStatusException e) {
                allStats = ExtHashSetOfQuasiStatuses.create(this.signature);
                commonStat = QuasiStatus.create(this.signature);
                allStats.add(commonStat);
            }
        }

        Iterator<Constraint<TRSTerm>> i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfQuasiStatuses<FunctionSymbol> newStats;
        while(i.hasNext() && result==true) {
            c = i.next();
            try {
                //System.out.print(c + ": ");

                newStats = this.QRPOS(c, commonStat);
                /* newStats contains the extensions of commonStat that solve c */
                if(newStats.size()==0) {
                    if(this.QRPOS(c, QuasiStatus.create(Qoset.create(this.signature),
                            StatusMap.create(this.signature))).size()==0) {
                        //System.out.println("Not satisfiable by any QRPOS!");
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
            catch (QuasiStatusException excp) {
                this.crit = c;
                result = false;
            }
        }

        if(result==true) {
            Iterator<QuasiStatus<FunctionSymbol>> j = allStats.iterator();
            if(j.hasNext()) {
                /* just take an arbitrary status */
                QuasiStatus<FunctionSymbol> finalStatus = j.next();
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
    private ExtHashSetOfQuasiStatuses<FunctionSymbol> QRPOS(Constraint<TRSTerm> c, QuasiStatus<FunctionSymbol> stat) throws QuasiStatusException {
        //     AProVETime.checkTimer();

        TRSTerm origL = c.getLeft();
        TRSTerm origR = c.getRight();
        ExtHashSetOfQuasiStatuses<FunctionSymbol> res = ExtHashSetOfQuasiStatuses.create(this.signature);
        QuasiStatus<FunctionSymbol> newStat;

        QRPOS qrpos = QRPOS.create(stat.getPrecedence(),
                stat.getStatusMap());
        if(qrpos.solves(c)) {
            /* the current status suffices */
            res.add(stat);
            return res;
        }
        if(qrpos.inRelation(origR, origL)) {
            /* it won't work */
            return res;
        }

        if(Multiterm.create(origL, stat.getStatusMap(), stat.getPrecedence()).equals(
                Multiterm.create(origR, stat.getStatusMap(), stat.getPrecedence()))) {
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
            return QRPOS.minimalEqualizers(origL, origR, stat, this.equiv);
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
                    catch(QuasiStatusException e) {
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

        if(symbLeft.equals(symbRight) || stat.areEquivalent(symbLeft, symbRight)) {
            if(((FunctionSymbol)symbLeft).getArity()==1
                    &&((FunctionSymbol)symbRight).getArity()==1) {
                res = res.union(this.QRPOS(Constraint.create(l.getArgument(0),
                        r.getArgument(0),
                        OrderRelation.GR),
                        stat));
                if(c.getType()==OrderRelation.GE) {
                    res=res.union(QRPOS.minimalGENGRs(l, r, stat, this.equiv)).minimalElements();
                }
                return res.minimalElements();
            }

            if(stat.hasMultisetStatus(symbLeft) && stat.hasMultisetStatus(symbRight)) {
                MultiSet<TRSTerm> argL = new HashMultiSet<TRSTerm>(l.getArguments());
                MultiSet<TRSTerm> argR = new HashMultiSet<TRSTerm>(r.getArguments());
                MultisetExtension mul = MultisetExtension.create(qrpos);

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

                    DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses<FunctionSymbol>> dh = DoubleHash.create();
                    Iterator<TRSTerm> le = LVector.iterator();
                    Iterator<TRSTerm> re;

                    while(le.hasNext()) {
                        re = RVector.iterator();
                        newLeft = le.next();
                        while(re.hasNext()) {
                            newRight = re.next();
                            dh.put(newLeft, newRight,
                                    this.QRPOS(Constraint.create(newLeft, newRight, OrderRelation.GE),
                                            stat));
                        }
                    }

                    int i;
                    ExtHashSetOfQuasiStatuses<FunctionSymbol> newRes;
                    ExtHashSetOfQuasiStatuses<FunctionSymbol> finalRes;
                    QuasiStatus<FunctionSymbol> testStat;
                    for (Sequence s : SequenceGenerator.create(sizeR, sizeL)) {
                        //    AProVETime.checkTimer();
                        newStat = stat.deepcopy();
                        newRes = ExtHashSetOfQuasiStatuses.create(this.signature);
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
                            finalRes = ExtHashSetOfQuasiStatuses.create(this.signature);
                            Iterator<QuasiStatus<FunctionSymbol>> j = newRes.iterator();
                            while(j.hasNext()) {
                                testStat = j.next();
                                mul = MultisetExtension.create(QRPOS.create(
                                        testStat.getPrecedence(),
                                        testStat.getStatusMap()));
                                if(mul.relate(argL, argR)==OrderRelation.GR) {
                                    finalRes.add(testStat);
                                }
                            }
                            if(!finalRes.isEmpty()) {
                                res = res.union(finalRes).minimalElements();
                            }
                        }
                    }
                }

                if(c.getType()==OrderRelation.GE) {
                    res=res.union(QRPOS.minimalGENGRs(l, r, stat, this.equiv)).minimalElements();
                }

                return res.minimalElements();
            }

            else {
                /* try all permutations */
                boolean synEq = symbLeft.equals(symbRight);
                List<Permutation> lefts = null;
                List<Permutation> rights = null;
                Iterable<Permutation> permsLeft;
                Iterable<Permutation> permsRight;

                int n = ((FunctionSymbol) symbLeft).getArity();
                int m = ((FunctionSymbol) symbRight).getArity();

                int min = Math.min(n, m);

                if(stat.hasPermutation(symbLeft)) {
                    lefts = new ArrayList<Permutation>(1);
                    lefts.add(stat.getPermutation(symbLeft));
                    permsLeft = lefts;
                }
                else {
                    permsLeft = PermutationGenerator.create(n);
                }

                if(synEq || stat.hasPermutation(symbRight)) {
                    rights = new ArrayList<Permutation>();
                    if(stat.hasPermutation(symbRight)) {
                        rights.add(stat.getPermutation(symbRight));
                    }
                }

                TRSFunctionApplication permL;
                TRSFunctionApplication permR;
                ExtHashSetOfQuasiStatuses<FunctionSymbol> newRes;
                DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses<FunctionSymbol>> dh = DoubleHash.create();
                DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses<FunctionSymbol>> equalizers = DoubleHash.create();

                e1 = l.getArguments().iterator();
                while(e1.hasNext()) {
                    /* compare corresponding subterms l_i, r_i and
                     * also compare l to r_i
                     */

                    newLeft = (TRSTerm) e1.next();

                    e2 = r.getArguments().iterator();
                    while(e2.hasNext()) {
                        newRight = (TRSTerm) e2.next();
                        dh.put(newLeft, newRight,
                                this.QRPOS(Constraint.create(newLeft, newRight, OrderRelation.GR),
                                        stat));
                        dh.put(l, newRight,
                                this.QRPOS(Constraint.create(l, newRight, OrderRelation.GR),
                                        stat));
                        equalizers.put(newLeft, newRight,
                                QRPOS.minimalGENGRs(newLeft, newRight, stat, this.equiv));
                    }
                }

                for (Permutation pLeft : permsLeft) {

                    if(stat.hasPermutation(symbRight)) {
                        permsRight = rights;
                    }
                    else if(synEq) {
                        /* use the same permutation */
                        rights.clear();
                        rights.add(pLeft);
                        permsRight = rights;
                    }
                    else {
                        permsRight = PermutationGenerator.create(m);
                    }

                    for (Permutation pRight : permsRight) {

                        newStat = stat.deepcopy();
                        newStat.assignPermutation(symbLeft, pLeft);
                        newStat.assignPermutation(symbRight, pRight);

                        QRPOS testqrpos = QRPOS.create(newStat.getPrecedence(),
                                newStat.getStatusMap());
                        if(testqrpos.inRelation(l, r)) {
                            res.add(newStat);
                        }
                        else {
                            permL = LPOS.permuteTerm(l, pLeft);
                            permR = LPOS.permuteTerm(r, pRight);

                            for(int i=0; i<min; i++) {
                                newRes = ExtHashSetOfQuasiStatuses.create(this.signature);
                                newRes.add(newStat.deepcopy());
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
                                while(j < m && !newRes.isEmpty()) {
                                    newRight = permR.getArgument(j);
                                    newRes = newRes.mergeAll(dh.get(l, newRight)).minimalElements();
                                    j++;
                                }

                                if(!newRes.isEmpty()) {
                                    res = res.union(newRes);
                                }
                            }

                            if(m < n) {
                                /* special case: out of arguments for r while having >= */
                                newStat = stat.deepcopy();
                                newRes = ExtHashSetOfQuasiStatuses.create(this.signature);
                                newRes.add(newStat);
                                int j = 0;
                                while (j < m && !newRes.isEmpty()) {
                                    newLeft = permL.getArgument(j);
                                    newRight = permR.getArgument(j);
                                    newRes = newRes.mergeAll(equalizers.get(newLeft, newRight)).minimalElements();
                                    j++;
                                }
                                res = res.union(newRes);
                            }
                        }
                    }
                }

                /* multiset status */
                if(!stat.hasPermutation(symbLeft) && !stat.hasPermutation(symbRight)) {
                    newStat = stat.deepcopy();
                    newStat.assignMultisetStatus(symbLeft);
                    newStat.assignMultisetStatus(symbRight);
                    res = res.union(this.QRPOS(c, newStat)).minimalElements();
                }
            }

            /* and don't forget (2a)! */
            e1 = l.getArguments().iterator();

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.QRPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(QRPOS.minimalGENGRs(l, r, stat, this.equiv)).minimalElements();
            }

            return res.minimalElements();
        }

        else if(stat.isGreater(symbLeft, symbRight)) {
            /* (2c), no need for (2a) */

            e2 = r.getArguments().iterator();

            newStat = stat.deepcopy();
            res.add(newStat);
            while(e2.hasNext() && !res.isEmpty()) {
                newRight = (TRSTerm) e2.next();
                res = res.mergeAll(this.QRPOS(Constraint.create(l, newRight, OrderRelation.GR), newStat)).minimalElements();
                newStat = res.intersectAll();
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(QRPOS.minimalGENGRs(l, r, stat, this.equiv)).minimalElements();
            }

            return res.minimalElements();
        }

        else if(stat.isGreater(symbRight, symbLeft)) {
            /* try (2a) */
            e1 = l.getArguments().iterator();

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.QRPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(QRPOS.minimalGENGRs(l, r, stat, this.equiv)).minimalElements();
            }

            return res.minimalElements();
        }

        else {
            /* symbRight and symbLeft are incomparable */

            /* enrich the precedence by symbLeft | symbRight
             or by setting symbLeft and symbRight equivalent
             */
            if(!stat.isMinimal(symbLeft)) {
                newStat = stat.deepcopy();
                newStat.setGreater(symbLeft, symbRight);

                res = this.QRPOS(c, newStat);
            }

            newStat = stat.deepcopy();
            if(this.equiv==null || this.equiv.contains(Doubleton.create(symbLeft, symbRight))) {
                try {
                    newStat.setEquivalent(symbLeft, symbRight);
                    res = res.union(this.QRPOS(c, newStat)).minimalElements();
                }
                catch (QuasiStatusException e) {
                    /* nope! */
                }
            }

            /* and don't forget (2a)! */
            e1 = l.getArguments().iterator();

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.QRPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(QRPOS.minimalGENGRs(l, r, stat, this.equiv)).minimalElements();
            }

            return res.minimalElements();
        }
    }

}
