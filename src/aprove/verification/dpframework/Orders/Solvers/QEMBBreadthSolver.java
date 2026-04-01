package aprove.verification.dpframework.Orders.Solvers ;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/** New QEMB-solver, calcultes all (minimal) precedences
 * that solve the constraints.
 *
 *   @author      Stephan Falke
 *   @version $Id$
 */

public class QEMBBreadthSolver implements AbortableConstraintSolver<TRSTerm>, ProvidesCriticalConstraint {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private Qoset<FunctionSymbol> finalPrecedence;
    private ExtHashSetOfQosets<FunctionSymbol> initialPrecedences;
    private ExtHashSetOfQosets<FunctionSymbol> allFinalPrecedences;
    private Constraint<TRSTerm> crit;
    private Collection<Doubleton<FunctionSymbol>> equiv;

    /* constructors */

    private QEMBBreadthSolver(List<FunctionSymbol> signature, ExtHashSetOfQosets<FunctionSymbol> initialPrecedences, Collection<Doubleton<FunctionSymbol>> equiv) {
        this.signature = signature;
        this.initialPrecedences = initialPrecedences;
        this.equiv = equiv;
        this.finalPrecedence = null;
        this.allFinalPrecedences = null;
        this.crit = null;
    }

    /** Creates a new instance of <code>QEMBBreadthSolver</code>.
     * @param signature   the names of the symbols
     */
    public static QEMBBreadthSolver create(Set<FunctionSymbol> signature) {
        return new QEMBBreadthSolver(new ArrayList<FunctionSymbol>(signature), null, null);
    }

    /** Creates a new instance of <code>QEMBBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedences   the initial precedences
     */
    public static QEMBBreadthSolver create(Set<FunctionSymbol> signature,
            ExtHashSetOfQosets<FunctionSymbol> initialPrecedences) {
        return new QEMBBreadthSolver(new ArrayList<FunctionSymbol>(signature),
                initialPrecedences, null);
    }

    /** Creates a new instance of <code>QEMBBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QEMBBreadthSolver create(Set<FunctionSymbol> signature, Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QEMBBreadthSolver(new ArrayList<FunctionSymbol>(signature), null, equiv);
    }

    /** Creates a new instance of <code>QEMBBreadthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedences   the initial precedences
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QEMBBreadthSolver create(Set<FunctionSymbol> signature,
            ExtHashSetOfQosets<FunctionSymbol> initialPrecedences,
            Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QEMBBreadthSolver(new ArrayList<FunctionSymbol>(signature),
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
    public ExtHashSetOfQosets<FunctionSymbol> getAllFinalPrecedences() {
        return this.allFinalPrecedences;
    }

    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            return QEMB.create(this.finalPrecedence);
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
            return QEMB.create(this.finalPrecedence);
        }
        else {
            return null;
        }
    }

    /* return 'true' if the rules are ordered by the lexicographic path order,
     * return 'false' otherwise.
     * The lexicographic path order is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       there exists an 1<=i<=n such that
     *                       s_1 = t_1, ... ,s_i-1=t_i-1, s_i>t_i and
     *                       s>t_j for all i<j<=n
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     *   | is the strict part of a quasi order of the function symbols and is
     *   generated 'on the fly' with this implementation,
     *   ~ is the equivalence part of that qoset
     */
    private boolean tryToOrder() {
        boolean result = true;
        this.finalPrecedence = null;
        this.allFinalPrecedences = null;

        /* commonPrec will contain the intersection of the precedences that
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
                newPrecs = this.QEMB(c, commonPrec);
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
            catch (QosetException excp) {
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

        /* commonPrec will contain the intersection of the precedences that
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
            c = (Constraint<TRSTerm>)i.next();
            try {
                //System.out.print(c + ": ");

                newPrecs = this.QEMB(c, commonPrec);
                /* newPrecs contains the extensions of commonPrec that solve c */
                if(newPrecs.size()==0) {
                    if(this.QEMB(c, Qoset.create(this.signature)).size()==0) {
                        //System.out.println("Not satisfiable by any QEMB!");
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
            catch (QosetException excp) {
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

    /** Returns the first constraint that could not be satisfied.
     */
    @Override
    public Constraint<TRSTerm> getCriticalConstraint() {
        return this.crit;
    }

    /* returns the extensions of prec that solve c */
    private ExtHashSetOfQosets<FunctionSymbol> QEMB(Constraint<TRSTerm> c, Qoset<FunctionSymbol> prec) throws QosetException {
        TRSTerm origL = c.getLeft();
        TRSTerm origR = c.getRight();
        ExtHashSetOfQosets<FunctionSymbol> res = ExtHashSetOfQosets.create(this.signature);
        Qoset<FunctionSymbol> newPrec;

        QEMB qemb = QEMB.create(prec);
        if(qemb.solves(c)) {
            /* the current precedence suffices */
            res.add(prec);
            return res;
        }
        if(qemb.inRelation(origR, origL)) {
            /* it won't work */
            return res;
        }

        if(QLPO.quasiEqual(origL, origR, prec)) {
            /* (1) is not true -> check for strictness */
            if (c.getType()==OrderRelation.GR) {
                /* it won't work, so return empty set of qosets */
                return res;
            }
            else {
                /* the current precedence suffices */
                res.add(prec);
                return res;
            }
        }

        if(c.getType()==OrderRelation.EQ) {
            return QLPO.minimalEqualizers(origL, origR, prec, this.equiv);
        }

        if(origL.isVariable()) {
            /* it won't work, so return empty set of qosets */
            return res;
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
                /* it won't work, so return empty set of qosets */
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
            e1 = l.getArguments().iterator();
            e2 = r.getArguments().iterator();

            ExtHashSetOfQosets<FunctionSymbol> newRes = ExtHashSetOfQosets.create(this.signature);
            newRes.add(prec);
            while(e1.hasNext() && !newRes.isEmpty()) {
                newLeft = (TRSTerm)e1.next();
                newRight = (TRSTerm)e2.next();
                newRes = newRes.mergeAll(this.QEMB(Constraint.create(newLeft, newRight, OrderRelation.GE), newRes.intersectAll())).minimalElements();
            }

            Iterator<Qoset<FunctionSymbol>> i = newRes.iterator();
            Qoset<FunctionSymbol> testPrec;
            while(i.hasNext()) {
                testPrec = i.next();
                if(!QLPO.quasiEqual(l, r, testPrec)) {
                    res.add(testPrec);
                }
            }

            /* and don't forget non-strict (2a)! */
            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.QEMB(Constraint.create(newLeft, r, OrderRelation.GE), prec));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(QLPO.minimalEqualizers(l, r, prec, this.equiv));
            }

            return res.minimalElements();
        }

        else {
            /* symbRightName and symbLeftName are neither equal nor equivalent */

            /* enrich the precedence by equivalence of symbLeftName and symbRightName */
            if(((FunctionSymbol)symbLeft).getArity()==((FunctionSymbol)symbRight).getArity() &&
                    (this.equiv==null || this.equiv.contains(Doubleton.create(symbLeft, symbRight)))) {
                newPrec = prec.deepcopy();

                try {
                    newPrec.setEquivalent(symbLeft, symbRight);
                    res = res.union(this.QEMB(c, newPrec));
                }
                catch(QosetException e) {
                    /* nop */
                }
            }

            /* and don't forget non-strict (2a)! */
            e1 = l.getArguments().iterator();

            while(e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.QEMB(Constraint.create(newLeft, r, OrderRelation.GE), prec));
            }

            if(c.getType()==OrderRelation.GE) {
                res=res.union(QLPO.minimalEqualizers(l, r, prec, this.equiv));
            }

            return res.minimalElements();
        }
    }

}
