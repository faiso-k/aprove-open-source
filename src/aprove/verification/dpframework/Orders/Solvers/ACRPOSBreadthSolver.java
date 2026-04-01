package aprove.verification.dpframework.Orders.Solvers ;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.DoubleHash;
import aprove.verification.dpframework.Orders.Utility.FlattenedMultiterm;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** New ACRPOS-solver, calculates all (minimal) statuses
 * that solve the constraints.
 *
 *   @author      Stephan Falke
 *   @version $Id$
 */

public class ACRPOSBreadthSolver implements ConstraintSolver<TRSTerm>, ProvidesCriticalConstraint, AbortableConstraintSolver<TRSTerm> {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private List<FunctionSymbol> Asignature;
    private List<FunctionSymbol> ACsignature;
    private List<FunctionSymbol> Csignature;
    private ExtHashSetOfStatuses<FunctionSymbol> initialStatuses;
    private Poset<FunctionSymbol> finalPrecedence;
    private StatusMap<FunctionSymbol> finalStatusMap;
    private ExtHashSetOfStatuses<FunctionSymbol> allFinalStatuses;
    private Constraint<TRSTerm> crit;
    private boolean lex, onlyLR, mul, flat;

    /* constructors */

    private ACRPOSBreadthSolver(List<FunctionSymbol> signature, List<FunctionSymbol> Asignature, List<FunctionSymbol> ACsignature, List<FunctionSymbol> Csignature, ExtHashSetOfStatuses<FunctionSymbol> initialStatuses, boolean lex, boolean onlyLR, boolean mul, boolean flat) {
        this.signature = signature;
        this.Asignature = Asignature;
        this.ACsignature = ACsignature;
        this.Csignature = Csignature;
        this.initialStatuses = initialStatuses;
        this.finalPrecedence = null;
        this.finalStatusMap = null;
        this.allFinalStatuses = null;
        this.crit = null;
        this.lex = lex;
        this.onlyLR = onlyLR;
        this.mul = mul;
        this.flat = flat;
    }

    /** Creates a new instance of <code>ACRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param Asignature  the names of the A symbols
     * @param ACsignature  the names of the AC symbols
     * @param Csignature  the names of the C symbols
     */
    public static ACRPOSBreadthSolver create(List<FunctionSymbol> signature, List<FunctionSymbol> Asignature, List<FunctionSymbol> ACsignature, List<FunctionSymbol> Csignature) {
        return new ACRPOSBreadthSolver(new ArrayList<FunctionSymbol>(signature), new ArrayList<FunctionSymbol>(Asignature), new ArrayList<FunctionSymbol>(ACsignature), new ArrayList<FunctionSymbol>(Csignature), null, true, false, true, true);
    }

    /** Creates a new instance of <code>ACRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param Asignature  the names of the A symbols
     * @param ACsignature   the names of the AC symbols
     * @param Csignature   the names of the C symbols
     * @param initialStatuses    the initial statuses
     */
    public static ACRPOSBreadthSolver create(List<FunctionSymbol> signature, List<FunctionSymbol> Asignature, List<FunctionSymbol> ACsignature, List<FunctionSymbol> Csignature,
            ExtHashSetOfStatuses<FunctionSymbol> initialStatuses) {
        return new ACRPOSBreadthSolver(new ArrayList<FunctionSymbol>(signature), new ArrayList<FunctionSymbol>(Asignature), new ArrayList<FunctionSymbol>(ACsignature), new ArrayList<FunctionSymbol>(Csignature), initialStatuses, true, false, true, true);
    }

    /** Creates a new instance of <code>ACRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param Asignature  the names of the A symbols
     * @param ACsignature   the names of the AC symbols
     * @param Csignature   the names of the C symbols
     * @param lex   allow/disallow lexicographic comparisons for non-ACnC symbols
     * @param onlyLR   if true, only use lexicographic comparison from left to right
     * @param mul   allow/disallow multiset comparison for non-ACnC symbols
     * @param flat   allow/disallow flat comparison for binary non-ACnC symbols
     */
    public static ACRPOSBreadthSolver create(List<FunctionSymbol> signature, List<FunctionSymbol> Asignature, List<FunctionSymbol> ACsignature, List<FunctionSymbol> Csignature,
            boolean lex, boolean onlyLR, boolean mul, boolean flat) {
        return new ACRPOSBreadthSolver(new ArrayList<FunctionSymbol>(signature), new ArrayList<FunctionSymbol>(Asignature), new ArrayList<FunctionSymbol>(ACsignature), new ArrayList<FunctionSymbol>(Csignature), null, lex, onlyLR, mul, flat);
    }

    /** Creates a new instance of <code>ACRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param Asignature  the names of the A symbols
     * @param ACsignature   the names of the AC symbols
     * @param Csignature   the names of the C symbols
     * @param initialStatuses    the initial statuses
     * @param lex   allow/disallow lexicographic comparisons for non-ACnC symbols
     * @param onlyLR   if true, only use lexicographic comparison from left to right
     * @param mul   allow/disallow multiset comparison for non-ACnC symbols
     * @param flat   allow/disallow flat comparison for binary non-ACnC symbols
     */
    public static ACRPOSBreadthSolver create(List<FunctionSymbol> signature, List<FunctionSymbol> Asignature, List<FunctionSymbol> ACsignature, List<FunctionSymbol> Csignature,
            ExtHashSetOfStatuses<FunctionSymbol> initialStatuses,
            boolean lex, boolean onlyLR, boolean mul, boolean flat) {
        return new ACRPOSBreadthSolver(new ArrayList<FunctionSymbol>(signature), new ArrayList<FunctionSymbol>(Asignature), new ArrayList<FunctionSymbol>(ACsignature), new ArrayList<FunctionSymbol>(Csignature), initialStatuses, lex, onlyLR, mul, flat);
    }

    /** Returns a final precedence, <code>null</code> if the constraints
     * couldn't be solved.
     */
    public Poset getFinalPrecedence() {
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
    public ExtHashSetOfStatuses getAllFinalStatuses() {
        return this.allFinalStatuses;
    }

    @Override
    public Order<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            return ACRPOS.create(this.finalPrecedence, this.finalStatusMap);
        }
        else {
            return null;
        }
    }

    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            return ACRPOS.create(this.finalPrecedence, this.finalStatusMap);
        }
        else {
            return null;
        }
    }

    /** Verbose version of <code>solve</code>.
     * @see #solve(Set<Constraint>)
     */
    public Order<TRSTerm> verboseSolve(Set<Constraint<TRSTerm>> cs) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.verboseTryToOrder()) {
            return ACRPOS.create(this.finalPrecedence, this.finalStatusMap);
        }
        else {
            return null;
        }
    }

    /*
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
     *
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
            Iterator<FunctionSymbol> i = this.ACsignature.iterator();
            while(i.hasNext()) {
                commonStat.assignFlatStatus(i.next());
            }
            i = this.Asignature.iterator();
            while(i.hasNext()) {
                commonStat.assignFlatStatus(i.next());
            }
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
                Iterator<FunctionSymbol> i = this.ACsignature.iterator();
                while(i.hasNext()) {
                    commonStat.assignFlatStatus(i.next());
                }
                i = this.Asignature.iterator();
                while(i.hasNext()) {
                    commonStat.assignFlatStatus(i.next());
                }
                allStats.add(commonStat);
            }
        }

        Iterator<Constraint<TRSTerm>> i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfStatuses<FunctionSymbol> newStats;
        while(i.hasNext() && result==true) {
            c = i.next();
            try {
                newStats = this.ACRPOS(c, commonStat);
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
            if(!allStats.isEmpty()) {
                /* just take an arbitrary status */
                Status<FunctionSymbol> finalStatus = allStats.iterator().next();
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
            Iterator<FunctionSymbol> i = this.ACsignature.iterator();
            while(i.hasNext()) {
                commonStat.assignFlatStatus(i.next());
            }
            i = this.Asignature.iterator();
            while(i.hasNext()) {
                commonStat.assignFlatStatus(i.next());
            }
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
                Iterator<FunctionSymbol> i = this.ACsignature.iterator();
                while(i.hasNext()) {
                    commonStat.assignFlatStatus(i.next());
                }
                i = this.Asignature.iterator();
                while(i.hasNext()) {
                    commonStat.assignFlatStatus(i.next());
                }
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

                newStats = this.ACRPOS(c, commonStat);
                /* newStats contains the extensions of commonStat that solve c */
                if(newStats.size()==0) {
                    if(this.ACRPOS(c, Status.create(Poset.create(this.signature),
                            StatusMap.create(this.signature))).size()==0) {
                        //System.out.println("Not satisfiable by any ACRPOS!");
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
            if(!allStats.isEmpty()) {
                /* just take an arbitrary status */
                Status<FunctionSymbol> finalStatus = allStats.iterator().next();
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
    private ExtHashSetOfStatuses<FunctionSymbol> ACRPOS(Constraint<TRSTerm> c, Status<FunctionSymbol> stat) throws StatusException {
        //    AProVETime.checkTimer();
        TRSTerm origL = c.getLeft();
        TRSTerm origR = c.getRight();
        ExtHashSetOfStatuses<FunctionSymbol> res = ExtHashSetOfStatuses.create(this.signature);
        Status<FunctionSymbol> newStat;

        ACRPOS acrpos = ACRPOS.create(stat.getPrecedence(),
                stat.getStatusMap());
        if(acrpos.solves(c)) {
            /* the current status suffices */
            res.add(stat);
            return res;
        }
        if(acrpos.inRelation(origR, origL)) {
            /* it won't work */
            return res;
        }

        if(FlattenedMultiterm.create(origL, stat.getStatusMap()).equals(FlattenedMultiterm.create(origR, stat.getStatusMap()))) {
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
            return ACRPOS.minimalEqualizers(origL, origR, stat, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature).minimalElements();
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

        Iterator<? extends TRSTerm> e1;
        Iterator<? extends TRSTerm> e2;
        FunctionSymbol symbLeft = l.getRootSymbol();
        FunctionSymbol symbRight = r.getRootSymbol();
        TRSTerm newLeft;
        TRSTerm newRight;

        if(symbLeft.equals(symbRight)) {
            if(((FunctionSymbol)symbLeft).getArity()==1) {
                res = res.union(this.ACRPOS(Constraint.create(l.getArgument(0),
                        r.getArgument(0),
                        OrderRelation.GR),
                        stat));
                if(c.getType()==OrderRelation.GE) {
                    res=res.union(ACRPOS.minimalGENGRs(l, r, stat, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
                }
                return res.minimalElements();
            }

            if(stat.hasMultisetStatus(symbLeft)) {
                MultiSet<TRSTerm> argL = new HashMultiSet<TRSTerm>(l.getArguments());
                MultiSet<TRSTerm> argR = new HashMultiSet<TRSTerm>(r.getArguments());
                MultisetExtension mul = MultisetExtension.create(acrpos);

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
                                    this.ACRPOS(Constraint.create(newLeft, newRight, OrderRelation.GE),
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
                                mul = MultisetExtension.create(ACRPOS.create(
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
                    res=res.union(ACRPOS.minimalGENGRs(l, r, stat, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
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
                            ACRPOS.minimalGENGRs(newLeft, newRight, stat, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature));
                    dh.put(newLeft, newRight, this.ACRPOS(Constraint.create(newLeft, newRight, OrderRelation.GR),
                            stat));
                    dh.put(l, newRight, this.ACRPOS(Constraint.create(l, newRight, OrderRelation.GR),
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
                    res = res.union(this.ACRPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
                }

                if(c.getType()==OrderRelation.GE) {
                    res=res.union(ACRPOS.minimalGENGRs(l, r, stat, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
                }

                return res.minimalElements();
            }

            else if(stat.hasFlatStatus(symbLeft)) {
                /* Oh well... */

                FlattenedMultiterm flatLeft = FlattenedMultiterm.create(l, stat.getStatusMap());
                FlattenedMultiterm flatRight = FlattenedMultiterm.create(r, stat.getStatusMap());

                /* l > r' for all r' from embNoBig(r) */
                Iterator<FlattenedMultiterm> ee = flatRight.getMultiArguments().keySet().iterator();
                Set<FunctionSymbol> symbs = new LinkedHashSet<FunctionSymbol>();
                while(ee.hasNext()) {
                    FlattenedMultiterm fmt = (FlattenedMultiterm)ee.next();
                    if(!fmt.isVariable() && !stat.isGreater(fmt.getRootSymbol(), symbLeft)) {
                        symbs.add((FunctionSymbol) fmt.getRootSymbol());
                    }
                }
                List<FunctionSymbol> symbsvec = new ArrayList<FunctionSymbol>(symbs);
                int nn = symbsvec.size();
                for (Sequence theSeq : SequenceGenerator.create(nn, 2)) {
                    Status<FunctionSymbol> statstat = stat.deepcopy();
                    boolean ok = true;
                    for(int num=0; ok && num<nn; num++) {
                        if(theSeq.get(num)==1) {
                            try {
                                statstat.setGreater(symbsvec.get(num), symbLeft);
                            }
                            catch(StatusException e) {
                                ok = false;
                            }
                        }
                    }
                    if(ok) {
                        ExtHashSetOfStatuses<FunctionSymbol> embNoBig = ExtHashSetOfStatuses.create(this.signature);
                        embNoBig.add(statstat);
                        Iterator i = flatRight.embNoBig(statstat.getPrecedence()).iterator();
                        try {
                            while(i.hasNext()) {
                                embNoBig = embNoBig.mergeAll(this.ACRPOS(Constraint.create(l, ((FlattenedMultiterm)i.next()).toTerm(), OrderRelation.GR), embNoBig.intersectAll())).minimalElements();
                            }
                        }
                        catch(StatusException e) {
                            return ExtHashSetOfStatuses.create(this.signature);
                        }
                        res.addAll(embNoBig);
                    }
                }

                if(res.isEmpty()) {
                    return res;
                }

                /* noSmallHead(l) >>_{pf} noSmallHead(r) */
                MultiSet<TRSTerm> argL = new HashMultiSet<TRSTerm>(FlattenedMultiterm.toTerm(flatLeft.noSmallHead(stat.getPrecedence())));
                MultiSet<TRSTerm> argR = new HashMultiSet<TRSTerm>(FlattenedMultiterm.toTerm(flatRight.noSmallHead(stat.getPrecedence())));
                MultisetExtension mul = MultisetExtension.create(new ACRPOSf(acrpos, symbLeft));

                OrderRelation tmpRes = mul.relate(argL, argR);
                ExtHashSetOfStatuses<FunctionSymbol> noSmallHead = ExtHashSetOfStatuses.create(this.signature);
                if(tmpRes==OrderRelation.GR || tmpRes==OrderRelation.EQ) {
                    /* the current precedence suffices */
                    noSmallHead.add(stat);
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
                        newLeft = le.next();
                        while(re.hasNext()) {
                            newRight = re.next();
                            ExtHashSetOfStatuses<FunctionSymbol> tmpres = this.ACRPOS(Constraint.create(newLeft, newRight, OrderRelation.GE), stat);
                            ExtHashSetOfStatuses<FunctionSymbol> resi = ExtHashSetOfStatuses.create(this.signature);
                            /* modify the statuses if needed */
                            Iterator<Status<FunctionSymbol>> k = tmpres.iterator();
                            FunctionSymbol leftName;
                            if (newLeft.isVariable()) {
                                leftName = null;
                            } else {
                                leftName = ((TRSFunctionApplication)newLeft).getRootSymbol();
                            }
                            FunctionSymbol rightName;
                            if (newRight.isVariable()) {
                                rightName = null;
                            } else {
                                rightName = ((TRSFunctionApplication)newRight).getRootSymbol();
                            }
                            while(k.hasNext()) {
                                Status<FunctionSymbol> teststat = k.next();
                                if(leftName == null || rightName == null || leftName.equals(rightName) || teststat.isGreater(leftName, symbLeft) || teststat.isGreater(leftName, rightName)) {
                                    resi.add(teststat);
                                }
                                else {
                                    Status<FunctionSymbol> modified = teststat.deepcopy();
                                    try {
                                        modified.setGreater(leftName, symbLeft);
                                        resi.add(modified);
                                    }
                                    catch(StatusException execp) {
                                    }
                                    modified = teststat.deepcopy();
                                    try {
                                        modified.setGreater(leftName, rightName);
                                        resi.add(modified);
                                    }
                                    catch(StatusException execp) {
                                    }
                                }
                            }
                            dh.put(newLeft, newRight, resi.minimalElements());
                        }
                    }

                    /* maybe some elements of RVector should be small after all */
                    re = RVector.iterator();
                    while(re.hasNext()) {
                        newRight = re.next();
                        ExtHashSetOfStatuses<FunctionSymbol> small = ExtHashSetOfStatuses.create(this.signature);
                        try {
                            if(!newRight.isVariable()) {
                                /* not for variables */
                                newStat = stat.deepcopy();
                                newStat.setGreater(symbLeft, ((TRSFunctionApplication)newRight).getRootSymbol());
                                small.add(newStat);
                            }
                            dh.put(l, newRight, small);
                        }
                        catch(StatusException e) {
                        }
                    }

                    LVector.add(l);
                    int k;
                    ExtHashSetOfStatuses<FunctionSymbol> newRes;
                    Status<FunctionSymbol> testStat;
                    for (Sequence s : SequenceGenerator.create(sizeR, sizeL+1)) {
                        //    AProVETime.checkTimer();
                        newStat = stat.deepcopy();
                        newRes = ExtHashSetOfStatuses.create(this.signature);
                        newRes.add(newStat);
                        k = 0;
                        while(k < sizeR && !newRes.isEmpty()) {
                            newLeft = LVector.get(s.get(k));
                            newRight = RVector.get(k);
                            newRes = newRes.mergeAll(dh.get(newLeft, newRight)).minimalElements();
                            k++;
                        }
                        if(!newRes.isEmpty()) {
                            /* is it OK? */
                            Iterator<Status<FunctionSymbol>> j = newRes.iterator();
                            while(j.hasNext()) {
                                testStat = j.next();
                                MultiSet<TRSTerm> newArgR = new HashMultiSet<TRSTerm>(argR);
                                Iterator<TRSTerm> e = argR.keySet().iterator();
                                while(e.hasNext()) {
                                    newRight = e.next();
                                    if(!newRight.isVariable()) {
                                        if(testStat.isGreater(symbLeft, ((TRSFunctionApplication)newRight).getRootSymbol())) {
                                            newArgR.removeAny(newRight);
                                        }
                                    }
                                }
                                MultiSet<TRSTerm> newArgL = new HashMultiSet<TRSTerm>(argL);
                                e = argL.keySet().iterator();
                                while(e.hasNext()) {
                                    newLeft = e.next();
                                    if(!newLeft.isVariable()) {
                                        if(testStat.isGreater(symbLeft, ((TRSFunctionApplication)newLeft).getRootSymbol())) {
                                            newArgL.removeAny(newLeft);
                                        }
                                    }
                                }

                                mul = MultisetExtension.create(new ACRPOSf(ACRPOS.create(
                                        testStat.getPrecedence(),
                                        testStat.getStatusMap()),
                                        symbLeft));
                                OrderRelation tmpres = mul.relate(newArgL, newArgR);
                                if(tmpres==OrderRelation.GR || tmpres==OrderRelation.EQ) {
                                    noSmallHead.add(testStat);
                                }
                            }
                        }
                    }
                }

                res = res.mergeAll(noSmallHead).minimalElements();

                if(res.isEmpty()) {
                    return res;
                }

                SymbolicPolynomial leftPol = SymbolicPolynomial.createSymbolicPolynomial(flatLeft);
                SymbolicPolynomial rightPol = SymbolicPolynomial.createSymbolicPolynomial(flatRight);

                OrderRelation cmp = leftPol.compareToPositive(rightPol);
                if(cmp!=OrderRelation.GR) {
                    /* if it's > we're done */
                    /* bigHead(l) >> bigHead(r)? */
                    ExtHashSetOfStatuses<FunctionSymbol> finalRes = ExtHashSetOfStatuses.create(this.signature);
                    newStat = res.intersectAll();
                    MultiSet<TRSTerm> leftBig = new HashMultiSet<TRSTerm>(FlattenedMultiterm.toTerm(flatLeft.bigHead(newStat.getPrecedence())));
                    MultiSet<TRSTerm> rightBig = new HashMultiSet<TRSTerm>(FlattenedMultiterm.toTerm(flatRight.bigHead(newStat.getPrecedence())));

                    ACRPOS testacrpos = ACRPOS.create(newStat);
                    if(MultisetExtension.create(testacrpos).relate(leftBig, rightBig)==OrderRelation.GR) {
                        finalRes.add(newStat);
                    }
                    else {
                        MultiSet<TRSTerm> embNoSmallLeft = new HashMultiSet<TRSTerm>(FlattenedMultiterm.toTerm(flatLeft.noSmallHead(newStat.getPrecedence())));

                        List<TRSTerm> LVector = embNoSmallLeft.toList();

                        /* maybe some elements of LVector should be big    after all */
                        /* collect root symbols */
                        List<FunctionSymbol> roots = new ArrayList<FunctionSymbol>();
                        for (TRSTerm t : LVector) {
                            if(!t.isVariable()) {
                                roots.add(((TRSFunctionApplication)t).getRootSymbol());
                            }
                        }

                        Iterator<Status<FunctionSymbol>> i;
                        int n = roots.size();
                        for (Sequence s : SequenceGenerator.create(n, 2)) {
                            //    AProVETime.checkTimer();
                            Status<FunctionSymbol> newerStat = newStat.deepcopy();
                            try {
                                for(int k=0; k<n; k++) {
                                    if(s.get(k)==1) {
                                        newerStat.setGreater(roots.get(k), symbLeft);
                                    }
                                }

                                i = res.iterator();
                                while(i.hasNext()) {
                                    Status<FunctionSymbol> oldstat = i.next();
                                    Status<FunctionSymbol> teststat = oldstat.merge(newerStat);
                                    leftBig = new HashMultiSet<TRSTerm>(FlattenedMultiterm.toTerm(flatLeft.bigHead(teststat.getPrecedence())));
                                    rightBig = new HashMultiSet<TRSTerm>(FlattenedMultiterm.toTerm(flatRight.bigHead(teststat.getPrecedence())));
                                    testacrpos = ACRPOS.create(teststat);
                                    if(MultisetExtension.create(testacrpos).relate(leftBig, rightBig)==OrderRelation.GR) {
                                        finalRes.add(teststat);
                                    }
                                }
                            }
                            catch(StatusException e) {
                            }
                        }
                        finalRes = finalRes.minimalElements();
                    }

                    if(cmp==OrderRelation.GE) {
                        ExtHashSetOfStatuses<FunctionSymbol> newRes = ExtHashSetOfStatuses.create(this.signature);
                        argL = new HashMultiSet<TRSTerm>(FlattenedMultiterm.toTerm(flatLeft.getMultiArguments()));
                        argR = new HashMultiSet<TRSTerm>(FlattenedMultiterm.toTerm(flatRight.getMultiArguments()));
                        mul = MultisetExtension.create(acrpos);

                        OrderRelation mulres = mul.relate(argL, argR);
                        if(mulres==OrderRelation.GR) {
                            /* current precedence suffices */
                            newRes.add(stat);
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
                                newLeft = le.next();
                                while(re.hasNext()) {
                                    newRight = re.next();
                                    dh.put(newLeft, newRight, this.ACRPOS(Constraint.create(newLeft, newRight, OrderRelation.GE), stat));
                                }
                            }

                            int k;
                            Status<FunctionSymbol> testStat;
                            for (Sequence s : SequenceGenerator.create(sizeR, sizeL)) {
                                //    AProVETime.checkTimer();
                                newStat = stat.deepcopy();
                                ExtHashSetOfStatuses<FunctionSymbol> seqRes = ExtHashSetOfStatuses.create(this.signature);
                                seqRes.add(newStat);
                                k = 0;
                                while(k < sizeR && !seqRes.isEmpty()) {
                                    newLeft = LVector.get(s.get(k));
                                    newRight = RVector.get(k);
                                    seqRes = seqRes.mergeAll(dh.get(newLeft, newRight)).minimalElements();
                                    k++;
                                }

                                if(!seqRes.isEmpty()) {
                                    /* is it OK? */
                                    Iterator<Status<FunctionSymbol>> j = seqRes.iterator();
                                    while(j.hasNext()) {
                                        testStat = j.next();
                                        mul = MultisetExtension.create(ACRPOS.create(testStat.getPrecedence(), testStat.getStatusMap()));
                                        if(mul.relate(argL, argR)==OrderRelation.GR) {
                                            newRes.add(testStat);
                                        }
                                    }
                                }
                            }
                            finalRes = finalRes.union(newRes).minimalElements();
                        }
                    }
                    res = res.mergeAll(finalRes).minimalElements();
                }

                /* l' > r for some l' from embNoBig(l)? */
                Iterator i = flatLeft.embNoBig(stat.getPrecedence()).iterator();
                while(i.hasNext()) {
                    res = res.union(this.ACRPOS(Constraint.create(((FlattenedMultiterm)i.next()).toTerm(), r, OrderRelation.GR), stat)).minimalElements();
                }

                /* (2a) */
                Iterator<FlattenedMultiterm> e = flatLeft.getMultiArguments().keySet().iterator();
                while(e.hasNext()) {
                    res = res.union(this.ACRPOS(Constraint.create(e.next().toTerm(), r, OrderRelation.GR), stat)).minimalElements();
                }

                if(c.getType()==OrderRelation.GE) {
                    res=res.union(ACRPOS.minimalGENGRs(l, r, stat, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
                }

                return res.minimalElements();
            }

            else {
                /* try all permutations and multiset status and flat status */

                if(this.lex && !this.Csignature.contains(symbLeft)) {
                    int n = symbLeft.getArity();
                    Iterable<Permutation> perm;
                    if(this.onlyLR) {
                        Collection<Permutation> permList = new ArrayList<Permutation>();
                        int tmp[] = new int[n];
                        for(int i=0; i<n; i++) {
                            tmp[i] = i;
                        }
                        permList.add(Permutation.create(tmp));
                        perm = permList;
                    }
                    else {
                        /* all permutations */
                        perm = PermutationGenerator.create(n);
                    }
                    TRSFunctionApplication permL;
                    TRSFunctionApplication permR;
                    ExtHashSetOfStatuses<FunctionSymbol> newRes;
                    DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfStatuses<FunctionSymbol>> dh = DoubleHash.create();
                    DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfStatuses<FunctionSymbol>> equalizers = DoubleHash.create();

                    e1 = l.getArguments().iterator();
                    e2 = r.getArguments().iterator();
                    while(e1.hasNext()) {
                        /* compare corresponding subterms l_i, r_i and
                         * also compare l to r_i
                         */
                        newLeft = e1.next();
                        newRight = e2.next();
                        dh.put(newLeft, newRight,
                                this.ACRPOS(Constraint.create(newLeft, newRight, OrderRelation.GR),
                                        stat));
                        dh.put(l, newRight,
                                this.ACRPOS(Constraint.create(l, newRight, OrderRelation.GR),
                                        stat));
                        equalizers.put(newLeft, newRight,
                                ACRPOS.minimalGENGRs(newLeft, newRight, stat, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature));
                    }

                    for (Permutation p : perm) {
                        newStat = stat.deepcopy();
                        newStat.assignPermutation(symbLeft, p);

                        permL = LPOS.permuteTerm(l, p);
                        permR = LPOS.permuteTerm(r, p);
if(Globals.DEBUG_STEIN) {
    System.out.println("L: "+permL.toString()+"\n");
    System.out.println("R: "+permR.toString()+"\n\n");
}

                        for(int i=0; i<n; i++) {
                            newRes = ExtHashSetOfStatuses.create(this.signature);
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
                            while(j < n && !newRes.isEmpty()) {
                                newRight = permR.getArgument(j);
                                newRes = newRes.mergeAll(dh.get(l, newRight)).minimalElements();
                                j++;
                            }

                            if(!newRes.isEmpty()) {
                                res = res.union(newRes);
                            }
                        }
                    }
                }

                if(this.mul) {
                    /* multiset status */
                    newStat = stat.deepcopy();
                    newStat.assignMultisetStatus(symbLeft);
                    res = res.union(this.ACRPOS(c, newStat));
                }

                /* flat status */
                if(this.flat && ((FunctionSymbol)symbLeft).getArity()==2) {
                    newStat = stat.deepcopy();
                    newStat.assignFlatStatus(symbLeft);
                    res = res.union(this.ACRPOS(c, newStat));
                }

                /* and don't forget (2a)! */
                e1 = l.getArguments().iterator();

                while(e1.hasNext()) {
                    newLeft = (TRSTerm) e1.next();
                    res = res.union(this.ACRPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
                }

                if(c.getType()==OrderRelation.GE) {
                    res=res.union(ACRPOS.minimalGENGRs(l, r, stat, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
                }

                return res.minimalElements();
            }
        }

        else if(stat.isGreater(symbLeft, symbRight)) {
            /* (2c), no need for (2a) */

            if(stat.hasFlatStatus(symbRight)) {
                Set<FlattenedMultiterm> mSet = FlattenedMultiterm.create(r, stat.getStatusMap()).getMultiArguments().keySet();
                Set<TRSTerm> tSet = new LinkedHashSet<TRSTerm>();
                for(FlattenedMultiterm mt:mSet)  {
                    tSet.add(mt.toTerm());
                }
                e2 = tSet.iterator();
            }
            else {
                e2 = r.getArguments().iterator();
            }

            newStat = stat.deepcopy();
            res.add(newStat);
            while(e2.hasNext() && !res.isEmpty()) {
                newRight = e2.next();
                res = res.mergeAll(this.ACRPOS(Constraint.create(l, newRight, OrderRelation.GR), newStat)).minimalElements();
                newStat = res.intersectAll();
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(ACRPOS.minimalGENGRs(l, r, stat, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
            }

            return res.minimalElements();
        }

        else if(stat.isGreater(symbRight, symbLeft)) {
            /* try (2a) */
            if(stat.hasFlatStatus(symbLeft)) {
                Set<FlattenedMultiterm> mSet = FlattenedMultiterm.create(l, stat.getStatusMap()).getMultiArguments().keySet();
                Set<TRSTerm> tSet = new LinkedHashSet<TRSTerm>();
                for(FlattenedMultiterm mt:mSet)  {
                    tSet.add(mt.toTerm());
                }
                e1 = tSet.iterator();
            }
            else {
                e1 = l.getArguments().iterator();
            }

            while(e1.hasNext()) {
                newLeft = e1.next();
                res = res.union(this.ACRPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(ACRPOS.minimalGENGRs(l, r, stat, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
            }

            return res.minimalElements();
        }

        else {
            /* symbRightName and symbLeftName are incomparable */

            /* enrich the precedence by symbLeftName | symbRightName */
            newStat = stat.deepcopy();
            newStat.setGreater(symbLeft, symbRight);

            res = this.ACRPOS(c, newStat);

            /* and don't forget (2a)! */
            if(stat.hasFlatStatus(symbLeft)) {
                 Set<FlattenedMultiterm> mSet = FlattenedMultiterm.create(l, stat.getStatusMap()).getMultiArguments().keySet();
                 Set<TRSTerm> tSet = new LinkedHashSet<TRSTerm>();
                 for(FlattenedMultiterm mt:mSet)  {
                     tSet.add(mt.toTerm());
                 }
                 e1 = tSet.iterator();
            }
            else {
                e1 = l.getArguments().iterator();
            }

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.ACRPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(ACRPOS.minimalGENGRs(l, r, stat, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
            }

            return res.minimalElements();
        }
    }

}
