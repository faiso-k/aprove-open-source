package aprove.verification.dpframework.Orders.Solvers ;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.DoubleHash;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** New QRPO-solver, calculates all (minimal) precedences
 * that solve the constraints.
 *
 *   @author      Stephan Falke
 *   @version $Id$
 */

public class QRPOBreadthSolver implements AbortableConstraintSolver<TRSTerm>, ProvidesCriticalConstraint {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private ExtHashSetOfQosets<FunctionSymbol> initialPrecedences;
    private Qoset<FunctionSymbol> finalPrecedence;
    private ExtHashSetOfQosets<FunctionSymbol> allFinalPrecedences;
    private Constraint<TRSTerm> crit;
    private Collection<Doubleton<FunctionSymbol>> equiv;

    /* constructors */

    private QRPOBreadthSolver(List<FunctionSymbol> signature, ExtHashSetOfQosets<FunctionSymbol> initialPrecedences, Collection<Doubleton<FunctionSymbol>> equiv) {
        this.signature = signature;
        this.initialPrecedences = initialPrecedences;
        this.equiv = equiv;
        this.finalPrecedence = null;
        this.allFinalPrecedences = null;
        this.crit = null;
    }

    /** Creates a new instance of <code>QRPOBreadthSolver</code>.
     * @param signature   the names of the symbols
     */
    public static QRPOBreadthSolver create(Set<FunctionSymbol> signature) {
        return new QRPOBreadthSolver(new ArrayList<FunctionSymbol>(signature), null, null);
    }

    /** Creates a new instance of <code>QRPOBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedences   the initial precedences
     */
    public static QRPOBreadthSolver create(Set<FunctionSymbol> signature,
            ExtHashSetOfQosets<FunctionSymbol> initialPrecedences) {
        return new QRPOBreadthSolver(new ArrayList<FunctionSymbol>(signature),
                initialPrecedences, null);
    }

    /** Creates a new instance of <code>QRPOBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QRPOBreadthSolver create(Set<FunctionSymbol> signature, Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QRPOBreadthSolver(new ArrayList<FunctionSymbol>(signature), null, equiv);
    }

    /** Creates a new instance of <code>NewQRPOSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedences   the initial precedences
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QRPOBreadthSolver create(Set<FunctionSymbol> signature,
            ExtHashSetOfQosets<FunctionSymbol> initialPrecedences,
            Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QRPOBreadthSolver(new ArrayList<FunctionSymbol>(signature),
                initialPrecedences, equiv);
    }

    /** Returns a final precedence, <code>null</code> if the constraints
     * couldn't be solved.
     */
    public Qoset<FunctionSymbol> getFinalPrecedence() {
        return this.finalPrecedence;
    }

    /** Returns all final precedences that solve the constraints,
     * <code>null</code> if no such precedence was found.
     */
    public ExtHashSetOfQosets getAllFinalPrecedences() {
        return this.allFinalPrecedences;
    }

    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            Qoset<FunctionSymbol> p = this.finalPrecedence.deepcopy();
            try {
                p.fix();
                return QRPO.create(p);
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
            return QRPO.create(this.finalPrecedence);
        }
        else {
            return null;
        }
    }

    /* return 'true' if the rules are ordered by the recursive path order
     * with non-strict precedence, return 'false' otherwise.
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m) and
     *                       {s_1, ... , s_n} >> {t_1, ... , t_m}
     *                       where >> is the multiset extension, if
     *                       f and g are equivalent
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     * Terms are considered equal their multiterms according to the precedence
     * are equal.
     * | is an partial order of the function symbols and is generated
     * 'on the fly' with this implementation.
     */
    private boolean tryToOrder() {
        boolean result = true;
        this.finalPrecedence = null;
        this.allFinalPrecedences = null;

        /* commonPrec will contain the intersection of the qosets that
         * solve the constraints considered so far, i.e. the relations in
         * commonPrec will have to be used in any case
         */
        Qoset<FunctionSymbol> commonPrec;
        ExtHashSetOfQosets<FunctionSymbol> allPrecs;

        if(this.initialPrecedences==null) {
            allPrecs = ExtHashSetOfQosets.create(this.signature);
            commonPrec = Qoset.create(this.signature);
            allPrecs.add(commonPrec);
        }
        else {
            try {
                allPrecs = this.initialPrecedences.deepcopy();
                commonPrec = allPrecs.intersectAll();
            }
            catch(QosetException e) {
                allPrecs = ExtHashSetOfQosets.create(this.signature);
                commonPrec = Qoset.create(this.signature);
                allPrecs.add(commonPrec);
            }
        }

        Iterator<Constraint<TRSTerm>> i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfQosets<FunctionSymbol> newPrecs;
        while(i.hasNext() && result==true) {
            c = i.next();
            try {
                newPrecs = this.QRPO(c, commonPrec);
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
            Iterator<Qoset<FunctionSymbol>> iqs = allPrecs.iterator();
            if(iqs.hasNext()) {
                /* just take an arbitrary precedence */
                this.finalPrecedence = iqs.next();
            }
            this.allFinalPrecedences = allPrecs;
        }

        return result;
    }

    private boolean verboseTryToOrder() {
        boolean result = true;
        this.finalPrecedence = null;
        this.allFinalPrecedences = null;

        /* commonPrec will contain the intersection of the qosets that
         * solve the constraints considered so far, i.e. the relations in
         * commonPrec will have to be used in any case
         */
        Qoset<FunctionSymbol> commonPrec;
        ExtHashSetOfQosets<FunctionSymbol> allPrecs;

        if(this.initialPrecedences==null) {
            allPrecs = ExtHashSetOfQosets.create(this.signature);
            commonPrec = Qoset.create(this.signature);
            allPrecs.add(commonPrec);
        }
        else {
            try {
                allPrecs = this.initialPrecedences.deepcopy();
                commonPrec = allPrecs.intersectAll();
            }
            catch(QosetException e) {
                allPrecs = ExtHashSetOfQosets.create(this.signature);
                commonPrec = Qoset.create(this.signature);
                allPrecs.add(commonPrec);
            }
        }

        Iterator<Constraint<TRSTerm>> i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfQosets<FunctionSymbol> newPrecs;
        while(i.hasNext() && result==true) {
            c = i.next();
            try {
                //System.out.print(c + ": ");

                newPrecs = this.QRPO(c, commonPrec);
                /* newPrecs contains the extensions of commonPrec that solve c */
                if(newPrecs.size()==0) {
                    if(this.QRPO(c, Qoset.create(this.signature)).size()==0) {
                        //System.out.println("Not satisfiable by any QRPO!");
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
            Iterator<Qoset<FunctionSymbol>> iqs = allPrecs.iterator();
            if(iqs.hasNext()) {
                /* just take an arbitrary qoset */
                this.finalPrecedence = iqs.next();
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
    private ExtHashSetOfQosets<FunctionSymbol> QRPO(Constraint<TRSTerm> c, Qoset<FunctionSymbol> prec) throws OrderedSetException {
        //    AProVETime.checkTimer();
        TRSTerm origL = c.getLeft();
        TRSTerm origR = c.getRight();
        ExtHashSetOfQosets<FunctionSymbol> res = ExtHashSetOfQosets.create(this.signature);
        Qoset<FunctionSymbol> newPrec;

        QRPO qrpo = QRPO.create(prec);
        if(qrpo.solves(c)) {
            /* the current precedence suffices */
            res.add(prec);
            return res;
        }
        if(qrpo.inRelation(origR, origL)) {
            /* it won't work */
            return res;
        }

        if(qrpo.areEquivalent(origL, origR)) {
            /* (1) is not true -> check for strictness */
            if (c.getType()==OrderRelation.GR) {
                /* it won't work, so return empty set of precedences */
                return res;
            }
            else {
                /* the current precedence suffices */
                res.add(prec);
                return res;
            }
        }

        if(c.getType()==OrderRelation.EQ) {
            return QRPO.minimalEqualizers(origL, origR, prec, this.equiv);
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
                    catch(QosetException e) {
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
                /* it won't work, so return empty set of precedences */
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

        if(symbLeft.equals(symbRight) || prec.areEquivalent(symbLeft, symbRight)) {
            /* this case must be handeled by (2b) */
            if(((FunctionSymbol)symbLeft).getArity()==1
                    &&((FunctionSymbol)symbLeft).getArity()==1) {
                res = res.union(this.QRPO(Constraint.create(l.getArgument(0),
                        r.getArgument(0),
                        OrderRelation.GR),
                        prec));
                if(c.getType()==OrderRelation.GE) {
                    res=res.union(QRPO.minimalGENGRs(l, r, prec, this.equiv));
                }

                return res.minimalElements();
            }
            else {
                MultiSet<TRSTerm> argL = new HashMultiSet<TRSTerm>(l.getArguments());
                MultiSet<TRSTerm> argR = new HashMultiSet<TRSTerm>(r.getArguments());
                MultisetExtension mul = MultisetExtension.create(qrpo);

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

                    DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfQosets<FunctionSymbol>> dh = DoubleHash.create();
                    Iterator<TRSTerm> le = LVector.iterator();
                    Iterator<TRSTerm> re;

                    while(le.hasNext()) {
                        re = RVector.iterator();
                        newLeft = le.next();
                        while(re.hasNext()) {
                            newRight = re.next();
                            dh.put(newLeft, newRight,
                                    this.QRPO(Constraint.create(newLeft, newRight, OrderRelation.GE),
                                            prec));
                        }
                    }

                    int i;
                    ExtHashSetOfQosets<FunctionSymbol> newRes;
                    ExtHashSetOfQosets<FunctionSymbol> finalRes;
                    Qoset<FunctionSymbol> testPrec;
                    for (Sequence s : SequenceGenerator.create(sizeR, sizeL)) {
                        //    AProVETime.checkTimer();
                        newPrec = prec.deepcopy();
                        newRes = ExtHashSetOfQosets.create(this.signature);
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
                            finalRes = ExtHashSetOfQosets.create(this.signature);
                            Iterator<Qoset<FunctionSymbol>> jqs = newRes.iterator();
                            while(jqs.hasNext()) {
                                testPrec = jqs.next();
                                mul = MultisetExtension.create(QRPO.create(testPrec));
                                if(mul.relate(argL, argR)==OrderRelation.GR) {
                                    finalRes.add(testPrec);
                                }
                            }
                            if(!finalRes.isEmpty()) {
                                res = res.union(finalRes);
                            }
                        }
                    }
                }

                if(c.getType()==OrderRelation.GE) {
                    res=res.union(QRPO.minimalGENGRs(l, r, prec, this.equiv)).minimalElements();
                }

                return res.minimalElements();
            }
        }
        else if(prec.isGreater(symbLeft, symbRight)) {
            /* (2c), no need for (2a) */

            e2 = r.getArguments().iterator();

            newPrec = prec.deepcopy();
            res.add(newPrec);
            while(e2.hasNext() && !res.isEmpty()) {
                newRight = (TRSTerm) e2.next();
                res = res.mergeAll(this.QRPO(Constraint.create(l, newRight, OrderRelation.GR), newPrec)).minimalElements();
                newPrec = res.intersectAll();
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(QRPO.minimalGENGRs(l, r, prec, this.equiv)).minimalElements();
            }

            return res.minimalElements();
        }

        else if(prec.isGreater(symbRight, symbLeft)) {
            /* try (2a) */
            e1 = l.getArguments().iterator();

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.QRPO(Constraint.create(newLeft, r, OrderRelation.GE), prec));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(QRPO.minimalGENGRs(l, r, prec, this.equiv)).minimalElements();
            }

            return res.minimalElements();
        }

        else {
            /* symbRightName and symbLeftName are incomparable */

            /* enrich the precedence by symbLeftName | symbRightName */
            if(!prec.isMinimal(symbLeft)) {
                newPrec = prec.deepcopy();
                newPrec.setGreater(symbLeft, symbRight);

                res = this.QRPO(c, newPrec);
            }

            /* equivalent? */
            if(this.equiv==null || this.equiv.contains(Doubleton.create(symbLeft, symbRight))) {
                try {
                    newPrec = prec.deepcopy();
                    newPrec.setEquivalent(symbLeft, symbRight);
                    res = res.union(this.QRPO(c, newPrec));
                }
                catch(QosetException e) {
                    /* nop */
                }
            }

            /* and don't forget (2a)! */
            e1 = l.getArguments().iterator();

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.QRPO(Constraint.create(newLeft, r, OrderRelation.GE), prec));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(QRPO.minimalGENGRs(l, r, prec, this.equiv)).minimalElements();
            }

            return res.minimalElements();
        }
    }

}
