package aprove.verification.dpframework.Orders.Solvers ;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.DoubleHash;
import aprove.verification.dpframework.Orders.Utility.FlattenedQuasiMultiterm;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** New ACQRPOS-solver, calculates all (minimal) statuses
 * that solve the constraints.
 *
 *   @author      Stephan Falke
 *   @version $Id$
 */

public class ACQRPOSBreadthSolver implements ConstraintSolver<TRSTerm>, ProvidesCriticalConstraint, AbortableConstraintSolver<TRSTerm> {

    private List<Constraint<TRSTerm>> constrs;
    private List<String> signature;
    private List<String> Asignature;
    private List<String> ACsignature;
    private List<String> Csignature;
    private Qoset<String> finalPrecedence;
    private ExtHashSetOfQuasiStatuses initialStatuses;
    private StatusMap finalStatusMap;
    private ExtHashSetOfQuasiStatuses allFinalStatuses;
    private Constraint<TRSTerm> crit;
    private Collection<Doubleton<String>> equiv;
    private boolean lex, onlyLR, mul, flat;


    /* constructors */

    private ACQRPOSBreadthSolver(List<String> signature, List<String> Asignature, List<String> ACsignature, List<String> Csignature, ExtHashSetOfQuasiStatuses initialStatuses, Collection<Doubleton<String>> equiv, boolean lex, boolean onlyLR, boolean mul, boolean flat) {
        this.signature = signature;
        this.Asignature = Asignature;
        this.ACsignature = ACsignature;
        this.Csignature = Csignature;
        this.initialStatuses = initialStatuses;
        this.equiv = equiv;
        this.finalPrecedence = null;
        this.finalStatusMap = null;
        this.allFinalStatuses = null;
        this.crit = null;
        this.lex = lex;
        this.onlyLR = onlyLR;
        this.mul = mul;
        this.flat = flat;
    }

    /** Creates a new instance of <code>ACQRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param Asignature  the names of the A symbols
     * @param ACsignature  the names of the AC symbols
     * @param Csignature  the names of the C symbols
     */
    public static ACQRPOSBreadthSolver create(List<String> signature, List<String> Asignature, List<String> ACsignature, List<String> Csignature) {
        return new ACQRPOSBreadthSolver(new ArrayList<String>(signature), new ArrayList<String>(Asignature), new ArrayList<String>(ACsignature), new ArrayList<String>(Csignature), null, null, true, false, true, true);
    }

    /** Creates a new instance of <code>ACQRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param Asignature  the names of the A symbols
     * @param ACsignature  the names of the AC symbols
     * @param Csignature  the names of the C symbols
     * @param initialStatuses    the initial statuses
     */
    public static ACQRPOSBreadthSolver create(List<String> signature, List<String> Asignature, List<String> ACsignature, List<String> Csignature,
            ExtHashSetOfQuasiStatuses initialStatuses) {
        return new ACQRPOSBreadthSolver(new ArrayList<String>(signature), new ArrayList<String>(Asignature), new ArrayList<String>(ACsignature), new ArrayList<String>(Csignature), initialStatuses, null, true, false, true, true);
    }

    /** Creates a new instance of <code>ACQRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param Asignature  the names of the A symbols
     * @param ACsignature  the names of the AC symbols
     * @param Csignature  the names of the C symbols
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static ACQRPOSBreadthSolver create(List<String> signature, List<String> Asignature, List<String> ACsignature, List<String> Csignature, Collection<Doubleton<String>> equiv) {
        return new ACQRPOSBreadthSolver(new ArrayList<String>(signature), new ArrayList<String>(Asignature), new ArrayList<String>(ACsignature), new ArrayList<String>(Csignature), null, equiv, true, false, true, true);
    }

    /** Creates a new instance of <code>ACQRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param Asignature  the names of the A symbols
     * @param ACsignature  the names of the AC symbols
     * @param Csignature  the names of the C symbols
     * @param initialStatuses    the initial statuses
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static ACQRPOSBreadthSolver create(List<String> signature, List<String> Asignature, List<String> ACsignature, List<String> Csignature,
            ExtHashSetOfQuasiStatuses initialStatuses,
            Collection<Doubleton<String>> equiv) {
        return new ACQRPOSBreadthSolver(new ArrayList<String>(signature), new ArrayList<String>(Asignature), new ArrayList<String>(ACsignature), new ArrayList<String>(Csignature), initialStatuses, equiv, true, false, true, true);
    }

    /** Creates a new instance of <code>ACQRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param Asignature  the names of the A symbols
     * @param ACsignature  the names of the AC symbols
     * @param Csignature  the names of the C symbols
     * @param initialStatuses    the initial statuses
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     * @param lex   allow/disallow lexicographic comparisons for non-ACnC symbols
     * @param onlyLR   if true, only use lexicographic comparison from left to right
     * @param mul   allow/disallow multiset comparison for non-ACnC symbols
     * @param flat   allow/disallow flat comparison for binary non-ACnC symbols
     */
    public static ACQRPOSBreadthSolver create(List<String> signature, List<String> Asignature, List<String> ACsignature, List<String> Csignature,
            ExtHashSetOfQuasiStatuses initialStatuses,
            Collection<Doubleton<String>> equiv,
            boolean lex, boolean onlyLR, boolean mul, boolean flat) {
        return new ACQRPOSBreadthSolver(new ArrayList<String>(signature), new ArrayList<String>(Asignature), new ArrayList<String>(ACsignature), new ArrayList<String>(Csignature), initialStatuses, equiv, lex, onlyLR, mul, flat);
    }

    /** Creates a new instance of <code>ACQRPOSBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param Asignature  the names of the A symbols
     * @param ACsignature  the names of the AC symbols
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     * @param lex   allow/disallow lexicographic comparisons for non-ACnC symbols
     * @param onlyLR   if true, only use lexicographic comparison from left to right
     * @param mul   allow/disallow multiset comparison for non-ACnC symbols
     * @param flat   allow/disallow flat comparison for binary non-ACnC symbols
     */
    public static ACQRPOSBreadthSolver create(List<String> signature, List<String> Asignature, List<String> ACsignature, List<String> Csignature,
            Collection<Doubleton<String>> equiv,
            boolean lex, boolean onlyLR, boolean mul, boolean flat) {
        return new ACQRPOSBreadthSolver(new ArrayList<String>(signature), new ArrayList<String>(Asignature), new ArrayList<String>(ACsignature), new ArrayList<String>(Csignature), null, equiv, lex, onlyLR, mul, flat);
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
    public Order<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            Qoset<String> p = this.finalPrecedence.deepcopy();
            try {
                p.fix();
                return ACQRPOS.create(p, this.finalStatusMap);
            }
            catch(OrderedSetException e) {
                return null;
            }
        }
        else {
            return null;
        }
    }

    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            Qoset<String> p = this.finalPrecedence.deepcopy();
            try {
                p.fix();
                return ACQRPOS.create(p, this.finalStatusMap);
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
     * @see #solve(Set<Constraint<Term>>)
     */
    public Order<TRSTerm> verboseSolve(Set<Constraint<TRSTerm>> cs) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.verboseTryToOrder()) {
            return ACQRPOS.create(this.finalPrecedence, this.finalStatusMap);
        }
        else {
            return null;
        }
    }

    /*
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
        QuasiStatus commonStat;
        ExtHashSetOfQuasiStatuses allStats;

        if(this.initialStatuses==null) {
            allStats = ExtHashSetOfQuasiStatuses.create(this.signature);
            commonStat = QuasiStatus.create(this.signature);
            Iterator i = this.ACsignature.iterator();
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
            catch(QuasiStatusException e) {
                allStats = ExtHashSetOfQuasiStatuses.create(this.signature);
                commonStat = QuasiStatus.create(this.signature);
                Iterator i = this.ACsignature.iterator();
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

        Iterator i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfQuasiStatuses newStats;
        while(i.hasNext() && result==true) {
            c = (Constraint<TRSTerm>)i.next();
            try {
                newStats = this.ACQRPOS(c, commonStat);
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
            i = allStats.iterator();
            if(i.hasNext()) {
                /* just take an arbitrary status */
                QuasiStatus finalStatus = (QuasiStatus)i.next();
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
        QuasiStatus commonStat;
        ExtHashSetOfQuasiStatuses allStats;

        if(this.initialStatuses==null) {
            allStats = ExtHashSetOfQuasiStatuses.create(this.signature);
            commonStat = QuasiStatus.create(this.signature);
            Iterator i = this.ACsignature.iterator();
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
            catch(QuasiStatusException e) {
                allStats = ExtHashSetOfQuasiStatuses.create(this.signature);
                commonStat = QuasiStatus.create(this.signature);
                Iterator i = this.ACsignature.iterator();
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

        Iterator i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfQuasiStatuses newStats;
        while(i.hasNext() && result==true) {
            c = (Constraint<TRSTerm>)i.next();
            try {
                //System.out.print(c + ": ");

                newStats = this.ACQRPOS(c, commonStat);
                /* newStats contains the extensions of commonStat that solve c */
                if(newStats.size()==0) {
                    if(this.ACQRPOS(c, QuasiStatus.create(Qoset.create(this.signature),
                            StatusMap.create(this.signature))).size()==0) {
                        //System.out.println("Not satisfiable by any ACQRPOS!");
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
            i = allStats.iterator();
            if(i.hasNext()) {
                /* just take an arbitrary status */
                QuasiStatus finalStatus = (QuasiStatus)i.next();
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
    private ExtHashSetOfQuasiStatuses ACQRPOS(Constraint<TRSTerm> c, QuasiStatus stat) throws QuasiStatusException {
        //    AProVETime.checkTimer();
        TRSTerm origL = c.getLeft();
        TRSTerm origR = c.getRight();
        ExtHashSetOfQuasiStatuses res = ExtHashSetOfQuasiStatuses.create(this.signature);
        QuasiStatus newStat;

        ACQRPOS acqrpos = ACQRPOS.create(stat.getPrecedence(),
                stat.getStatusMap());
        if(acqrpos.solves(c)) {
            /* the current status suffices */
            res.add(stat);
            return res;
        }
        if(acqrpos.inRelation(origR, origL)) {
            /* it won't work */
            return res;
        }

        if(FlattenedQuasiMultiterm.create(origL, stat.getStatusMap(), stat.getPrecedence()).equals(
                FlattenedQuasiMultiterm.create(origR, stat.getStatusMap(), stat.getPrecedence()))) {
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
            return ACQRPOS.minimalEqualizers(origL, origR, stat, this.equiv, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature);
        }

        if(origL.isVariable()) {
            if(!origR.isVariable() && c.getType()==OrderRelation.GE) {
                TRSFunctionApplication r = (TRSFunctionApplication)origR;
                FunctionSymbol rSymb = r.getRootSymbol();
                if(rSymb.getArity()==0) {
                    /* minimal constants are GE to variables */
                    String rSymbName = rSymb.getName();
                    newStat = stat.deepcopy();
                    boolean OK;
                    try {
                        newStat.setMinimal(rSymbName);
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
        String symbLeftName = symbLeft.getName();
        String symbRightName = symbRight.getName();
        TRSTerm newLeft;
        TRSTerm newRight;

        if(symbLeft.equals(symbRight) || stat.areEquivalent(symbLeftName, symbRightName)) {
            if(((FunctionSymbol)symbLeft).getArity()==1
                    &&((FunctionSymbol)symbRight).getArity()==1) {
                res = res.union(this.ACQRPOS(Constraint.create(l.getArgument(0),
                        r.getArgument(0),
                        OrderRelation.GR),
                        stat));
                if(c.getType()==OrderRelation.GE) {
                    res=res.union(ACQRPOS.minimalGENGRs(l, r, stat, this.equiv, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
                }
                return res.minimalElements();
            }

            if(stat.hasMultisetStatus(symbLeftName) && stat.hasMultisetStatus(symbRightName)) {
                MultiSet<TRSTerm> argL = new HashMultiSet<TRSTerm>(l.getArguments());
                MultiSet<TRSTerm> argR = new HashMultiSet<TRSTerm>(r.getArguments());
                MultisetExtension mul = MultisetExtension.create(acqrpos);

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

                    DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses> dh = DoubleHash.create();
                    Iterator<TRSTerm> le = LVector.iterator();
                    Iterator<TRSTerm> re;

                    while(le.hasNext()) {
                        re = RVector.iterator();
                        newLeft = (TRSTerm)le.next();
                        while(re.hasNext()) {
                            newRight = (TRSTerm)re.next();
                            dh.put(newLeft, newRight,
                                    this.ACQRPOS(Constraint.create(newLeft, newRight, OrderRelation.GE),
                                            stat));
                        }
                    }

                    SequenceGenerator seq = SequenceGenerator.create(sizeR, sizeL);
                    int i;
                    ExtHashSetOfQuasiStatuses newRes;
                    ExtHashSetOfQuasiStatuses finalRes;
                    QuasiStatus testStat;

                    for (Sequence s : seq) {
                        //    AProVETime.checkTimer();
                        newStat = stat.deepcopy();
                        newRes = ExtHashSetOfQuasiStatuses.create(this.signature);
                        newRes.add(newStat);
                        i = 0;
                        while(i < sizeR && !newRes.isEmpty()) {
                            newLeft = LVector.get(s.get(i));
                            newRight = RVector.get(i);
                            newRes = newRes.mergeAll((ExtHashSetOfQuasiStatuses)dh.get(newLeft, newRight)).minimalElements();
                            i++;
                        }
                        if(!newRes.isEmpty()) {
                            /* maybe we did too much, i.e. the terms a equal */
                            finalRes = ExtHashSetOfQuasiStatuses.create(this.signature);
                            Iterator j = newRes.iterator();
                            while(j.hasNext()) {
                                testStat = (QuasiStatus)j.next();
                                mul = MultisetExtension.create(ACQRPOS.create(
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
                    res=res.union(ACQRPOS.minimalGENGRs(l, r, stat, this.equiv, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
                }

                return res.minimalElements();
            }

            if(stat.hasFlatStatus(symbLeftName) && stat.hasFlatStatus(symbRightName)) {
                /* Oh well... */
                QuasiStatus origStat = stat.deepcopy();
                ExtHashSetOfQuasiStatuses sickFinalRes = ExtHashSetOfQuasiStatuses.create(this.signature);

                /* consider all possibilities of equivalences */
                FlattenedQuasiMultiterm sflat = FlattenedQuasiMultiterm.create(l, stat.getStatusMap(), stat.getPrecedence());
                FlattenedQuasiMultiterm tflat = FlattenedQuasiMultiterm.create(r, stat.getStatusMap(), stat.getPrecedence());

                Set<FunctionSymbol> roots = sflat.getReachableCandidates();
                roots.addAll(tflat.getReachableCandidates());

                List<String> rootsNames = new ArrayList<String>();
                Iterator it = roots.iterator();
                while(it.hasNext()) {
                    FunctionSymbol symb = (FunctionSymbol)it.next();
                    String name = symb.getName();
                    if(this.equiv==null || this.equiv.contains(Doubleton.create(symbLeftName, name))) {
                        rootsNames.add(name);
                    }
                }
                int n = rootsNames.size();

                Iterable<Sequence> seq;
                if(n==0) {
                    List<Sequence> sss = new ArrayList<Sequence>(1);
                    sss.add(Sequence.create(new int[]{2107}));
                    seq = sss;
                }
                else {
                    seq = SequenceGenerator.create(n, 2);
                }

                for (Sequence theSeq : seq) {
                    stat = origStat.deepcopy();
                    res = ExtHashSetOfQuasiStatuses.create(this.signature);
                    String name = null;
                    try {
                        for(int k=0; k<n; k++) {
                            name = (String)rootsNames.get(k);
                            if(theSeq.get(k)==1) {
                                stat.setEquivalent(symbLeftName, name);
                                stat.assignFlatStatus(name);
                            }
                        }
                    }
                    catch(QuasiStatusException e) {
                        continue;
                    }
                    ACQRPOS tester = ACQRPOS.create(stat.getPrecedence(), stat.getStatusMap());
                    if(tester.solves(c)) {
                        sickFinalRes.add(stat);
                        continue;
                    }

                    FlattenedQuasiMultiterm flatLeft = FlattenedQuasiMultiterm.create(l, stat.getStatusMap(), stat.getPrecedence());
                    FlattenedQuasiMultiterm flatRight = FlattenedQuasiMultiterm.create(r, stat.getStatusMap(), stat.getPrecedence());

                    /* l > r' for all r' from embNoBig(r) */
                    Iterator<FlattenedQuasiMultiterm> ee = flatRight.getMultiArguments().keySet().iterator();
                    Set<FunctionSymbol> symbs = new LinkedHashSet<FunctionSymbol>();
                    while(ee.hasNext()) {
                        FlattenedQuasiMultiterm fmt = (FlattenedQuasiMultiterm)ee.next();
                        if(!fmt.isVariable() && !stat.isGreater(fmt.getSymbol().getName(), symbLeftName)) {
                            symbs.add((FunctionSymbol) fmt.getSymbol());
                        }
                    }
                    List<FunctionSymbol> symbsvec = new ArrayList<FunctionSymbol>(symbs);
                    int nn = symbsvec.size();
                    for (Sequence theSeqi : SequenceGenerator.create(nn, 2)) {
                        QuasiStatus statstat = stat.deepcopy();
                        boolean ok = true;
                        for(int num=0; ok && num<nn; num++) {
                            if(theSeqi.get(num)==1) {
                                try {
                                    statstat.setGreater(((FunctionSymbol)symbsvec.get(num)).getName(), symbLeftName);
                                }
                                catch(QuasiStatusException e) {
                                    ok = false;
                                }
                            }
                        }
                        if(ok) {
                            ExtHashSetOfQuasiStatuses embNoBig = ExtHashSetOfQuasiStatuses.create(this.signature);
                            embNoBig.add(statstat);
                            Iterator i = flatRight.embNoBig(statstat.getPrecedence()).iterator();
                            try {
                                while(i.hasNext()) {
                                    embNoBig = embNoBig.mergeAll(this.ACQRPOS(Constraint.create(l, ((FlattenedQuasiMultiterm)i.next()).toTerm(), OrderRelation.GR), embNoBig.intersectAll())).minimalElements();
                                }
                            }
                            catch(QuasiStatusException e) {
                                ok = false;
                            }
                            if(ok) {
                                res.addAll(embNoBig);
                            }
                        }
                    }

                    if(res.isEmpty()) {
                        continue;
                    }

                    /* noSmallHead(l) >>_{pf} noSmallHead(r) */
                    MultiSet<TRSTerm> argL = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(flatLeft.noSmallHead(stat.getPrecedence())));
                    MultiSet<TRSTerm> argR = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(flatRight.noSmallHead(stat.getPrecedence())));
                    MultisetExtension mul = MultisetExtension.create(new ACQRPOSf(acqrpos, symbLeftName));

                    OrderRelation tmpRes = mul.relate(argL, argR);
                    ExtHashSetOfQuasiStatuses noSmallHead = ExtHashSetOfQuasiStatuses.create(this.signature);
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

                        DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses> dh = DoubleHash.create();
                        Iterator<TRSTerm>  le = LVector.iterator();
                        Iterator<TRSTerm>  re;

                        while(le.hasNext()) {
                            re = RVector.iterator();
                            newLeft = (TRSTerm)le.next();
                            while(re.hasNext()) {
                                newRight = (TRSTerm)re.next();
                                ExtHashSetOfQuasiStatuses tmpres = this.ACQRPOS(Constraint.create(newLeft, newRight, OrderRelation.GE), stat);
                                ExtHashSetOfQuasiStatuses resi = ExtHashSetOfQuasiStatuses.create(this.signature);
                                /* modify the statuses if needed */
                                Iterator k = tmpres.iterator();
                                String leftName;
                                if (newLeft.isVariable()) {
                                    leftName = ((TRSVariable)newLeft).getName();
                                } else {
                                    leftName = ((TRSFunctionApplication)newLeft).getRootSymbol().getName();
                                }
                                String rightName;
                                if (newRight.isVariable()) {
                                    rightName = ((TRSVariable)newRight).getName();
                                } else {
                                    rightName = ((TRSFunctionApplication)newRight).getRootSymbol().getName();
                                }
                                while(k.hasNext()) {
                                    QuasiStatus teststat = (QuasiStatus)k.next();
                                    if(newLeft.isVariable() || newRight.isVariable() || leftName.equals(rightName) || teststat.areEquivalent(leftName, rightName) || teststat.isGreater(leftName, symbLeftName) || teststat.isGreater(leftName, rightName)) {
                                        resi.add(teststat);
                                    }
                                    else {
                                        QuasiStatus modified = teststat.deepcopy();
                                        try {
                                            modified.setGreater(leftName, symbLeftName);
                                            resi.add(modified);
                                        }
                                        catch(QuasiStatusException execp) {
                                        }
                                        modified = teststat.deepcopy();
                                        try {
                                            modified.setGreater(leftName, rightName);
                                            resi.add(modified);
                                        }
                                        catch(QuasiStatusException execp) {
                                        }
                                        modified = teststat.deepcopy();
                                        try {
                                            if(this.equiv==null || this.equiv.contains(Doubleton.create(leftName, rightName))) {
                                                modified.setEquivalent(leftName, rightName);
                                                resi.add(modified);
                                            }
                                        }
                                        catch(QuasiStatusException execp) {
                                        }
                                    }
                                }
                                dh.put(newLeft, newRight, resi.minimalElements());
                            }
                        }

                        /* maybe some elements of RVector should be small after all */
                        re = RVector.iterator();
                        while(re.hasNext()) {
                            newRight = (TRSTerm)re.next();
                            ExtHashSetOfQuasiStatuses small = ExtHashSetOfQuasiStatuses.create(this.signature);
                            try {
                                if(!newRight.isVariable()) {
                                    /* not for variables */
                                    newStat = stat.deepcopy();
                                    newStat.setGreater(symbLeftName, ((TRSFunctionApplication)newRight).getRootSymbol().getName());
                                    small.add(newStat);
                                }
                                dh.put(l, newRight, small);
                            }
                            catch(QuasiStatusException e) {
                            }
                        }

                        LVector.add(l);
                        int k;
                        ExtHashSetOfQuasiStatuses newRes;
                        QuasiStatus testStat;

                        for (Sequence s : SequenceGenerator.create(sizeR, sizeL+1)) {
                            //    AProVETime.checkTimer();
                            newStat = stat.deepcopy();
                            newRes = ExtHashSetOfQuasiStatuses.create(this.signature);
                            newRes.add(newStat);
                            k = 0;
                            while(k < sizeR && !newRes.isEmpty()) {
                                newLeft = LVector.get(s.get(k));
                                newRight = RVector.get(k);
                                newRes = newRes.mergeAll((ExtHashSetOfQuasiStatuses)dh.get(newLeft, newRight)).minimalElements();
                                k++;
                            }
                            if(!newRes.isEmpty()) {
                                /* is it OK? */
                                Iterator j = newRes.iterator();
                                while(j.hasNext()) {
                                    testStat = (QuasiStatus)j.next();
                                    MultiSet<TRSTerm> newArgR = new HashMultiSet<TRSTerm>(argR);
                                    Iterator<TRSTerm> e = argR.keySet().iterator();
                                    while(e.hasNext()) {
                                        newRight = (TRSTerm)e.next();
                                        if(!newRight.isVariable()) {
                                            if(testStat.isGreater(symbLeftName, ((TRSFunctionApplication)newRight).getRootSymbol().getName())) {
                                                newArgR.removeAny(newRight);
                                            }
                                        }
                                    }
                                    MultiSet<TRSTerm> newArgL = new HashMultiSet<TRSTerm>(argL);
                                    e = argL.keySet().iterator();
                                    while(e.hasNext()) {
                                        newLeft = (TRSTerm)e.next();
                                        if(!newLeft.isVariable()) {
                                            if(testStat.isGreater(symbLeftName, ((TRSFunctionApplication)newLeft).getRootSymbol().getName())) {
                                                newArgL.removeAny(newLeft);
                                            }
                                        }
                                    }

                                    mul = MultisetExtension.create(new ACQRPOSf(ACQRPOS.create(
                                            testStat.getPrecedence(),
                                            testStat.getStatusMap()),
                                            symbLeftName));
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
                        continue;
                    }

                    SymbolicPolynomial leftPol = SymbolicPolynomial.createSymbolicPolynomial(flatLeft);
                    SymbolicPolynomial rightPol = SymbolicPolynomial.createSymbolicPolynomial(flatRight);

                    OrderRelation cmp = leftPol.compareToPositive(rightPol);
                    if(cmp!=OrderRelation.GR) {
                        /* if it's > we're done */
                        /* bigHead(l) >> bigHead(r)? */
                        ExtHashSetOfQuasiStatuses finalRes = ExtHashSetOfQuasiStatuses.create(this.signature);
                        newStat = res.intersectAll();
                        MultiSet<TRSTerm> leftBig = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(flatLeft.bigHead(newStat.getPrecedence())));
                        MultiSet<TRSTerm> rightBig = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(flatRight.bigHead(newStat.getPrecedence())));

                        ACQRPOS testacrpos = ACQRPOS.create(newStat);
                        if(MultisetExtension.create(testacrpos).relate(leftBig, rightBig)==OrderRelation.GR) {
                            finalRes.add(newStat);
                        }
                        else {
                            MultiSet<TRSTerm> embNoSmallLeft = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(flatLeft.noSmallHead(newStat.getPrecedence())));

                            List<TRSTerm> LVector = embNoSmallLeft.toList();

                            /* maybe some elements of LVector should be big after all */
                            /* collect root symbols */
                            List<String> roots2 = new ArrayList<String>();
                            Iterator i = LVector.iterator();
                            while(i.hasNext()) {
                                TRSTerm t = (TRSTerm)i.next();
                                if(!t.isVariable()) {
                                    roots2.add(((TRSFunctionApplication)t).getRootSymbol().getName());
                                }
                            }

                            int n2 = roots2.size();

                            for (Sequence s : SequenceGenerator.create(n2, 2)) {
                                //    AProVETime.checkTimer();
                                QuasiStatus newerStat = newStat.deepcopy();
                                try {
                                    for(int k=0; k<n2; k++) {
                                        if(s.get(k)==1) {
                                            newerStat.setGreater(roots2.get(k), symbLeftName);
                                        }
                                    }

                                    i = res.iterator();
                                    while(i.hasNext()) {
                                        QuasiStatus oldstat = (QuasiStatus)i.next();
                                        QuasiStatus teststat = oldstat.merge(newerStat);
                                        leftBig = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(flatLeft.bigHead(teststat.getPrecedence())));
                                        rightBig = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(flatRight.bigHead(teststat.getPrecedence())));
                                        testacrpos = ACQRPOS.create(teststat);
                                        if(MultisetExtension.create(testacrpos).relate(leftBig, rightBig)==OrderRelation.GR) {
                                            finalRes.add(teststat);
                                        }
                                    }
                                }
                                catch(QuasiStatusException e) {
                                }
                            }
                            finalRes = finalRes.minimalElements();
                        }

                        if(cmp==OrderRelation.GE) {
                            ExtHashSetOfQuasiStatuses newRes = ExtHashSetOfQuasiStatuses.create(this.signature);
                            argL = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(flatLeft.getMultiArguments()));
                            argR = new HashMultiSet<TRSTerm>(FlattenedQuasiMultiterm.toTerm(flatRight.getMultiArguments()));
                            mul = MultisetExtension.create(acqrpos);

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

                                DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses> dh = DoubleHash.create();
                                Iterator<TRSTerm> le = LVector.iterator();
                                Iterator<TRSTerm> re;

                                while(le.hasNext()) {
                                    re = RVector.iterator();
                                    newLeft = (TRSTerm)le.next();
                                    while(re.hasNext()) {
                                        newRight = (TRSTerm)re.next();
                                        dh.put(newLeft, newRight, this.ACQRPOS(Constraint.create(newLeft, newRight, OrderRelation.GE), stat));
                                    }
                                }

                                int k;
                                QuasiStatus testStat;

                                for (Sequence s : SequenceGenerator.create(sizeR, sizeL)) {
                                    //    AProVETime.checkTimer();
                                    newStat = stat.deepcopy();
                                    ExtHashSetOfQuasiStatuses seqRes = ExtHashSetOfQuasiStatuses.create(this.signature);
                                    seqRes.add(newStat);
                                    k = 0;
                                    while(k < sizeR && !seqRes.isEmpty()) {
                                        newLeft = LVector.get(s.get(k));
                                        newRight = RVector.get(k);
                                        seqRes = seqRes.mergeAll((ExtHashSetOfQuasiStatuses)dh.get(newLeft, newRight)).minimalElements();
                                        k++;
                                    }

                                    if(!seqRes.isEmpty()) {
                                        /* is it OK? */
                                        Iterator j = seqRes.iterator();
                                        while(j.hasNext()) {
                                            testStat = (QuasiStatus)j.next();
                                            mul = MultisetExtension.create(ACQRPOS.create(testStat.getPrecedence(), testStat.getStatusMap()));
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

                    sickFinalRes.addAll(res);
                }

                res = sickFinalRes;

                FlattenedQuasiMultiterm flatLeft = FlattenedQuasiMultiterm.create(l, stat.getStatusMap(), stat.getPrecedence());

                /* l' > r for some l' from embNoBig(l)? */
                Iterator<FlattenedQuasiMultiterm> i = flatLeft.embNoBig(stat.getPrecedence()).iterator();
                while(i.hasNext()) {
                    res = res.union(this.ACQRPOS(Constraint.create(((FlattenedQuasiMultiterm)i.next()).toTerm(), r, OrderRelation.GR), stat)).minimalElements();
                }

                /* (2a) */
                Iterator<FlattenedQuasiMultiterm> e = flatLeft.getMultiArguments().keySet().iterator();
                while(e.hasNext()) {
                    res = res.union(this.ACQRPOS(Constraint.create(((FlattenedQuasiMultiterm)e.next()).toTerm(), r, OrderRelation.GR), stat)).minimalElements();
                }

                if(c.getType()==OrderRelation.GE) {
                    res=res.union(ACQRPOS.minimalGENGRs(l, r, stat, this.equiv, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
                }

                return res.minimalElements();
            }

            if(this.lex && !stat.hasFlatStatus(symbLeftName) && !stat.hasMultisetStatus(symbLeftName)
                    && !stat.hasFlatStatus(symbRightName) && !stat.hasMultisetStatus(symbRightName)
                    && !this.Csignature.contains(symbLeftName) && !this.Csignature.contains(symbRightName)) {

                /* try all permutations */
                boolean synEq = symbLeftName.equals(symbRightName);
                List<Permutation> lefts = null;
                List<Permutation> rights = null;
                Iterable<Permutation> permsLeft;
                Iterable<Permutation> permsRight;

                int n = ((FunctionSymbol) symbLeft).getArity();
                int m = ((FunctionSymbol) symbRight).getArity();

                int min = Math.min(n, m);

                if(stat.hasPermutation(symbLeftName)) {
                    lefts = new ArrayList<Permutation>(1);
                    lefts.add(stat.getPermutation(symbLeftName));
                    permsLeft = lefts;
                }
                else {
                    if(this.onlyLR) {
                        List<Permutation> pp = new ArrayList<Permutation>(1);
                        int[] tmp = new int[n];
                        for(int i=0; i<n; i++) {
                            tmp[i] = i;
                        }
                        pp.add(Permutation.create(tmp));
                        permsLeft = pp;
                    }
                    else {
                        permsLeft = PermutationGenerator.create(n);
                    }
                }

                if(synEq || stat.hasPermutation(symbRightName)) {
                    rights = new ArrayList<Permutation>();
                    if(stat.hasPermutation(symbRightName)) {
                        rights.add(stat.getPermutation(symbRightName));
                    }
                }

                TRSFunctionApplication permL;
                TRSFunctionApplication permR;
                ExtHashSetOfQuasiStatuses newRes;
                DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses> dh = DoubleHash.create();
                DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQuasiStatuses> equalizers = DoubleHash.create();

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
                                this.ACQRPOS(Constraint.create(newLeft, newRight, OrderRelation.GR),
                                        stat));
                        dh.put(l, newRight,
                                this.ACQRPOS(Constraint.create(l, newRight, OrderRelation.GR),
                                        stat));
                        equalizers.put(newLeft, newRight,
                                ACQRPOS.minimalGENGRs(newLeft, newRight, stat, this.equiv, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature));
                    }
                }

                for (Permutation pLeft : permsLeft) {

                    if(stat.hasPermutation(symbRightName)) {
                        permsRight = rights;
                    }
                    else if(synEq) {
                        /* use the same permutation */
                        rights.clear();
                        rights.add(pLeft);
                        permsRight = rights;
                    }
                    else {
                        if(this.onlyLR) {
                            List<Permutation> pp = new ArrayList<Permutation>(1);
                            int[] tmp = new int[m];
                            for(int i=0; i<m; i++) {
                                tmp[i] = i;
                            }
                            pp.add(Permutation.create(tmp));
                            permsRight = pp;
                        }
                        else {
                            permsRight = PermutationGenerator.create(m);
                        }
                    }

                    for (Permutation pRight : permsRight) {

                        newStat = stat.deepcopy();
                        newStat.assignPermutation(symbLeftName, pLeft);
                        newStat.assignPermutation(symbRightName, pRight);

                        ACQRPOS testacqrpos = ACQRPOS.create(newStat.getPrecedence(),
                                newStat.getStatusMap());
                        if(testacqrpos.inRelation(l, r)) {
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
                                    newRes = newRes.mergeAll((ExtHashSetOfQuasiStatuses)equalizers.get(newLeft, newRight)).minimalElements();
                                    j++;
                                }
                                if(!newRes.isEmpty()) {
                                    newLeft = permL.getArgument(i);
                                    newRight = permR.getArgument(i);
                                    newRes = newRes.mergeAll((ExtHashSetOfQuasiStatuses)dh.get(newLeft, newRight)).minimalElements();
                                }
                                j=i+1;
                                while(j < m && !newRes.isEmpty()) {
                                    newRight = permR.getArgument(j);
                                    newRes = newRes.mergeAll((ExtHashSetOfQuasiStatuses)dh.get(l, newRight)).minimalElements();
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
                                    newRes = newRes.mergeAll((ExtHashSetOfQuasiStatuses) equalizers.get(newLeft, newRight)).minimalElements();
                                    j++;
                                }
                                res = res.union(newRes);
                            }
                        }
                    }
                }
            }

            /* multiset status */
            if(this.mul && !stat.hasPermutation(symbLeftName) && !stat.hasPermutation(symbRightName)
                    && !stat.hasFlatStatus(symbLeftName) && !stat.hasFlatStatus(symbRightName)) {
                newStat = stat.deepcopy();
                newStat.assignMultisetStatus(symbLeftName);
                newStat.assignMultisetStatus(symbRightName);
                res = res.union(this.ACQRPOS(c, newStat)).minimalElements();
            }

            /* flat status */
            if(this.flat && !stat.hasPermutation(symbLeftName) && !stat.hasPermutation(symbRightName)
                    && !stat.hasMultisetStatus(symbLeftName) && !stat.hasMultisetStatus(symbRightName)
                    && ((FunctionSymbol)symbLeft).getArity()==2 && ((FunctionSymbol)symbRight).getArity()==2) {
                newStat = stat.deepcopy();
                newStat.assignFlatStatus(symbLeftName);
                newStat.assignFlatStatus(symbRightName);
                res = res.union(this.ACQRPOS(c, newStat)).minimalElements();
            }

            /* and don't forget (2a)! */
            e1 = l.getArguments().iterator();

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.ACQRPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(ACQRPOS.minimalGENGRs(l, r, stat, this.equiv, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
            }

            return res.minimalElements();
        }

        else if(stat.isGreater(symbLeftName, symbRightName)) {
            /* (2c), no need for (2a) */
            if(stat.hasFlatStatus(symbRightName)) {
                e2 = FlattenedQuasiMultiterm.create(r, stat.getStatusMap(), stat.getPrecedence()).getMultiArguments().keySet().iterator();
            }
            else {
                e2 = r.getArguments().iterator();
            }

            newStat = stat.deepcopy();
            res.add(newStat);
            while(e2.hasNext() && !res.isEmpty()) {
                newRight = (TRSTerm) e2.next();
                res = res.mergeAll(this.ACQRPOS(Constraint.create(l, newRight, OrderRelation.GR), newStat)).minimalElements();
                newStat = res.intersectAll();
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(ACQRPOS.minimalGENGRs(l, r, stat, this.equiv, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
            }

            return res.minimalElements();
        }

        else if(stat.isGreater(symbRightName, symbLeftName)) {
            /* try (2a) */
            if(stat.hasFlatStatus(symbLeftName)) {
                e1 = FlattenedQuasiMultiterm.create(l, stat.getStatusMap(), stat.getPrecedence()).getMultiArguments().keySet().iterator();
            }
            else {
                e1 = l.getArguments().iterator();
            }

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.ACQRPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(ACQRPOS.minimalGENGRs(l, r, stat, this.equiv, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
            }

            return res.minimalElements();
        }

        else {
            /* symbRightName and symbLeftName are incomparable */

            /* enrich the precedence by symbLeftName | symbRightName
             or by setting symbLeftName and symbRightName equivalent
             */
            if(!stat.isMinimal(symbLeftName)) {
                newStat = stat.deepcopy();
                newStat.setGreater(symbLeftName, symbRightName);

                res = this.ACQRPOS(c, newStat);
            }

            newStat = stat.deepcopy();
            if((this.equiv==null || this.equiv.contains(Doubleton.create(symbLeftName, symbRightName)))
                    && !(((stat.hasFlatStatus(symbLeftName) || stat.hasFlatStatus(symbRightName)))
                            && (((FunctionSymbol)symbLeft).getArity()!=2 || ((FunctionSymbol)symbRight).getArity()!=2))) {
                try {
                    newStat.setEquivalent(symbLeftName, symbRightName);
                    res = res.union(this.ACQRPOS(c, newStat)).minimalElements();
                }
                catch (QuasiStatusException e) {
                    /* nope! */
                }
            }

            /* and don't forget (2a)! */
            if(stat.hasFlatStatus(symbLeftName)) {
                e1 = FlattenedQuasiMultiterm.create(l, stat.getStatusMap(), stat.getPrecedence()).getMultiArguments().keySet().iterator();
            }
            else {
                e1 = l.getArguments().iterator();
            }

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.ACQRPOS(Constraint.create(newLeft, r, OrderRelation.GE), stat));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(ACQRPOS.minimalGENGRs(l, r, stat, this.equiv, this.lex, this.onlyLR, this.mul, this.flat, this.Csignature)).minimalElements();
            }

            return res.minimalElements();
        }
    }

}
