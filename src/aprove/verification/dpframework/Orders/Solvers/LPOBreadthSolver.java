package aprove.verification.dpframework.Orders.Solvers;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.DoubleHash;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/** New LPO-solver, calcultes all (minimal) precedences
 * that solve the constraints.
 *
 *   @author      Stephan Falke
 *   @version $Id$
 */

public class LPOBreadthSolver implements AbortableConstraintSolver<TRSTerm>, ProvidesCriticalConstraint<TRSTerm> {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private ExtHashSetOfPosets<FunctionSymbol> initialPrecedences;
    private Poset<FunctionSymbol> finalPrecedence;
    private ExtHashSetOfPosets<FunctionSymbol> allFinalPrecedences;
    private Constraint<TRSTerm> crit;

    /* constructors */

    private LPOBreadthSolver(List<FunctionSymbol> signature, ExtHashSetOfPosets<FunctionSymbol> initialPrecedences) {
        this.signature = signature;
        this.initialPrecedences = initialPrecedences;
        this.finalPrecedence = null;
        this.allFinalPrecedences = null;
        this.crit = null;
    }

    /**
     * Creates a new instance of <code>NewLPOSolver</code>.
     * @return NewLPOSolver
     */
    public static LPOBreadthSolver create() {
        return new LPOBreadthSolver(new ArrayList<FunctionSymbol>(), null);
    }

    /** Creates a new instance of <code>NewLPOSolver</code>.
     * @param signature   the names of the symbols
     */
    public static LPOBreadthSolver create(Set<FunctionSymbol> signature) {
        return new LPOBreadthSolver(new ArrayList<FunctionSymbol>(signature), null);
    }

    /** Creates a new instance of <code>NewLPOSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedences   the initial precedences
     */
    public static LPOBreadthSolver create(Set<FunctionSymbol> signature, ExtHashSetOfPosets<FunctionSymbol> initialPrecedences) {
        return new LPOBreadthSolver(new ArrayList<FunctionSymbol>(signature), initialPrecedences);
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
        if (this.tryToOrder()) {
            return LPO.create(this.finalPrecedence);
        } else {
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
     *   | is an partial order of the function symbols and is generated
     *   'on the fly' with this implementation.
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

        if (this.initialPrecedences == null) {
            allPrecs = ExtHashSetOfPosets.create(this.signature);
            commonPrec = Poset.create(this.signature);
            allPrecs.add(commonPrec);
        } else {
            try {
                allPrecs = this.initialPrecedences.deepcopy();
                commonPrec = allPrecs.intersectAll();
            } catch (PosetException e) {
                allPrecs = ExtHashSetOfPosets.create(this.signature);
                commonPrec = Poset.create(this.signature);
                allPrecs.add(commonPrec);
            }
        }

        Iterator<Constraint<TRSTerm>> i = this.constrs.iterator();
        Constraint<TRSTerm> c;
        ExtHashSetOfPosets<FunctionSymbol> newPrecs;
        while (i.hasNext() && result == true) {
            c = i.next();
            try {
                newPrecs = this.LPO(c, commonPrec);
                /* newPrecs contains the extensions of commonPrec that solve c */
                if (newPrecs.size() == 0) {
                    /* this constraint can't be oriented */
                    this.crit = c;
                    result = false;
                } else {
                    allPrecs = allPrecs.mergeAll(newPrecs).minimalElements();
                    /* allPrecs are the minimal precedences that solve all
                     * constraints considered so far
                     */
                    if (allPrecs.size() == 0) {
                        this.crit = c;
                        result = false;
                    } else {
                        commonPrec = allPrecs.intersectAll();
                    }
                }
            } catch (OrderedSetException excp) {
                this.crit = c;
                result = false;
            }
        }

        if (result == true) {
            Iterator<Poset<FunctionSymbol>> ip = allPrecs.iterator();
            if (ip.hasNext()) {
                /* just take an arbitrary precedence */
                this.finalPrecedence = ip.next();
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
    private ExtHashSetOfPosets<FunctionSymbol> LPO(Constraint<TRSTerm> c, Poset<FunctionSymbol> prec) throws OrderedSetException {
        TRSTerm origL = c.getLeft();
        TRSTerm origR = c.getRight();
        ExtHashSetOfPosets<FunctionSymbol> res = ExtHashSetOfPosets.create(this.signature);
        Poset<FunctionSymbol> newPrec;

        LPO lpo = LPO.create(prec);
        if (lpo.solves(c)) {
            /* the current precedence suffices */
            res.add(prec);
            return res;
        }
        if (lpo.inRelation(origR, origL)) {
            /* it won't work */
            return res;
        }

        if (origL.equals(origR)) {
            /* (1) is not true -> check for strictness */
            if (c.getType() == OrderRelation.GR) {
                /* it won't work, so return empty set of posets */
                return res;
            } else {
                /* the current precedence suffices */
                res.add(prec);
                return res;
            }
        }

        if (c.getType() == OrderRelation.EQ) {
            /* nope! */
            return res;
        }

        if (origL.isVariable()) {
            if (!origR.isVariable() && c.getType() == OrderRelation.GE) {
                TRSFunctionApplication r = (TRSFunctionApplication)origR;
                FunctionSymbol rSymb = r.getRootSymbol();
                if (rSymb.getArity() == 0) {
                    /* minimal constants are GE to variables */
                    newPrec = prec.deepcopy();
                    boolean OK;
                    try {
                        newPrec.setMinimal(rSymb);
                        OK = true;
                    } catch (PosetException e) {
                        /* that didn't work... */
                        OK = false;
                    }
                    if (OK) {
                        res.add(newPrec);
                        return res;
                    } else {
                        /* empty */
                        return res;
                    }
                } else {
                    /* empty */
                    return res;
                }
            } else {
                /* empty */
                return res;
            }
        }

        /* l = f(l_1, ..., l_n) */
        if (origR.isVariable()) {
            if (origL.getVariables().contains(origR)) {
                /* the current precedence suffices */
                res.add(prec);
                return res;
            } else {
                /* it won't work, so return empty set of posets */
                return res;
            }
        }

        /* r = g(r_1, ..., r_m) */
        Iterator e1;
        Iterator e2;
        TRSFunctionApplication l = (TRSFunctionApplication)origL;
        TRSFunctionApplication r = (TRSFunctionApplication)origR;
        FunctionSymbol symbLeft = l.getRootSymbol();
        FunctionSymbol symbRight = r.getRootSymbol();
        TRSTerm newLeft;
        TRSTerm newRight;

        if (symbLeft.equals(symbRight)) {
            if (((FunctionSymbol) symbLeft).getArity() == 1) {
                res = res.union(this.LPO(Constraint.create(l.getArgument(0), r.getArgument(0), OrderRelation.GR), prec));

                if (c.getType() == OrderRelation.GE) {
                    res = res.union(LPO.minimalGENGRs(l, r, prec));
                }

                return res.minimalElements();
            }

            /* this case must be handeled by (2b) */
            DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfPosets<FunctionSymbol>> equalizers = DoubleHash.create();
            DoubleHash<TRSTerm,TRSTerm,ExtHashSetOfPosets<FunctionSymbol>> dh = DoubleHash.create();
            ExtHashSetOfPosets<FunctionSymbol> newRes;
            int n = symbLeft.getArity();

            e1 = l.getArguments().iterator();

            while (e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                e2 = r.getArguments().iterator();
                while (e2.hasNext()) {
                    newRight = (TRSTerm) e2.next();
                    equalizers.put(newLeft, newRight, LPO.minimalGENGRs(newLeft, newRight, prec));
                    dh.put(newLeft, newRight, this.LPO(Constraint.create(newLeft, newRight, OrderRelation.GR), prec));
                    dh.put(l, newRight, this.LPO(Constraint.create(l, newRight, OrderRelation.GR), prec));
                }
            }

            for (int i = 0; i < n; i++) {
                newPrec = prec.deepcopy();
                newRes = ExtHashSetOfPosets.create(this.signature);
                newRes.add(newPrec);
                int j = 0;
                while (j < i && !newRes.isEmpty()) {
                    newLeft = l.getArgument(j);
                    newRight = r.getArgument(j);
                    newRes = newRes.mergeAll(equalizers.get(newLeft, newRight)).minimalElements();
                    j++;
                }
                if (!newRes.isEmpty()) {
                    newLeft = l.getArgument(i);
                    newRight = r.getArgument(i);
                    newRes = newRes.mergeAll(dh.get(newLeft, newRight)).minimalElements();
                }
                j = i + 1;
                while (j < n && !newRes.isEmpty()) {
                    newRight = r.getArgument(j);
                    newRes = newRes.mergeAll(dh.get(l, newRight)).minimalElements();
                    j++;
                }

                if (!newRes.isEmpty()) {
                    res = res.union(newRes);
                }
            }

            /* and don't forget a non-strict (2a)! */
            e1 = l.getArguments().iterator();
            while (e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.LPO(Constraint.create(newLeft, r, OrderRelation.GE), prec));
            }

            if (c.getType() == OrderRelation.GE) {
                res = res.union(LPO.minimalGENGRs(l, r, prec));
            }

            return res.minimalElements();
        } else if (prec.isGreater(symbLeft, symbRight)) {
            /* (2c), no need for (2a) */

            e2 = r.getArguments().iterator();

            newPrec = prec.deepcopy();
            res.add(newPrec);
            while (e2.hasNext() && !res.isEmpty()) {
                newRight = (TRSTerm) e2.next();
                res = res.mergeAll(this.LPO(Constraint.create(l, newRight, OrderRelation.GR), newPrec)).minimalElements();
                newPrec = res.intersectAll();
            }

            if (c.getType() == OrderRelation.GE) {
                res = res.union(LPO.minimalGENGRs(l, r, prec));
            }

            return res.minimalElements();
        } else if (prec.isGreater(symbRight, symbLeft)) {
            /* try non strict (2a) */
            e1 = l.getArguments().iterator();

            while (e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.LPO(Constraint.create(newLeft, r, OrderRelation.GE), prec));
            }

            if (c.getType() == OrderRelation.GE) {
                res = res.union(LPO.minimalGENGRs(l, r, prec));
            }

            return res.minimalElements();
        } else {
            /* symbRightName and symbLeftName are incomparable */

            /* enrich the precedence by symbLeftNamy | symbRightName */
            newPrec = prec.deepcopy();
            newPrec.setGreater(symbLeft, symbRight);

            res = this.LPO(c, newPrec);

            /* and don't forget non strict (2a)! */
            e1 = l.getArguments().iterator();

            while (e1.hasNext()) {
                newLeft = (TRSTerm) e1.next();
                res = res.union(this.LPO(Constraint.create(newLeft, r, OrderRelation.GE), prec));
            }

            if (c.getType() == OrderRelation.GE) {
                res = res.union(LPO.minimalGENGRs(l, r, prec));
            }

            return res.minimalElements();
        }
    }

}
