package aprove.verification.dpframework.Orders.Solvers ;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/** QLPO-solver with full backtracking.
 * <p>
 * Starting from an specified initial or empty precedence,
 * </code>QLPOSolver</code> tries to solve the given constraints.
 * It'll extend the precedence if necessary.
 *
 *   @author      Stephan Falke, Peter Schneider-Kamp
 *   @version $Id$
 */

public class QLPODepthSolver implements AbortableConstraintSolver<TRSTerm> {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private Qoset<FunctionSymbol> initialPrecedence;
    private Qoset<FunctionSymbol> finalPrecedence;
    private Collection<Doubleton<FunctionSymbol>> equiv;

    /* constructors */

    private QLPODepthSolver(List<FunctionSymbol> signature, Qoset<FunctionSymbol> initialPrecedence, Collection<Doubleton<FunctionSymbol>> equiv) {
        this.signature = signature;
        this.initialPrecedence = initialPrecedence;
        this.equiv = equiv;
        this.finalPrecedence = null;
    }

    /** Creates a new instance of <code>QLPODepthSolver</code>.
     * @param signature   the names of the symbols
     */
    public static QLPODepthSolver create(Set<FunctionSymbol> signature) {
        return new QLPODepthSolver(new ArrayList<FunctionSymbol>(signature), null, null);
    }

    /** Creates a new instance of <code>QLPODepthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedence   the initial precedence
     */
    public static QLPODepthSolver create(Set<FunctionSymbol> signature,
            Qoset<FunctionSymbol> initialPrecedence) {
        return new QLPODepthSolver(new ArrayList<FunctionSymbol>(signature),
                initialPrecedence, null);
    }
    /** Creates a new instance of <code>QLPODepthSolver</code>.
     * @param signature   the names of the symbols
     * @param equiv       a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QLPODepthSolver create(Set<FunctionSymbol> signature, Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QLPODepthSolver(new ArrayList<FunctionSymbol>(signature), null, equiv);
    }

    /** Creates a new instance of <code>QLPODepthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedence   the initial precedence
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QLPODepthSolver create(Set<FunctionSymbol> signature,
            Qoset<FunctionSymbol> initialPrecedence,
            Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QLPODepthSolver(new ArrayList<FunctionSymbol>(signature),
                initialPrecedence, equiv);
    }

    /** Returns the final precedence, <code>null</code> if the constraints
     * couldn't be solved.
     */
    public Qoset<FunctionSymbol> getFinalPrecedence() {
        return this.finalPrecedence;
    }

    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            Qoset<FunctionSymbol> p = this.finalPrecedence.deepcopy();
            try {
                p.fix();
                return QLPO.create(p);
            }
            catch(OrderedSetException e) {
                return null;
            }
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
     *                  (2b) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n), f~g and
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
        Qoset<FunctionSymbol> precedence;

        if(this.initialPrecedence==null) {
            precedence = Qoset.create(this.signature);
        }
        else {
            precedence = this.initialPrecedence.deepcopy();
        }

        try {
            result = this.QLPO(this.constrs, precedence);
        }
        catch (OrderedSetException excp) {
            result = false;
        }

        return result;
    }

    private boolean QLPO(List<Constraint<TRSTerm>> constrs,
            Qoset<FunctionSymbol> precedence) throws OrderedSetException {
        //    AProVETime.checkTimer();

        boolean result=false;

        QLPO qlpo = QLPO.create(precedence);
        if(!constrs.isEmpty()) {
            /* remove constraints for which the current precedence suffices */
            List<Constraint<TRSTerm>> newConstrs = new ArrayList<Constraint<TRSTerm>>();
            for (Constraint<TRSTerm> con : constrs) {
                if(!qlpo.solves(con)) {
                    newConstrs.add(con);
                }
            }
            constrs = newConstrs;
        }

        /* check for reverse relation*/
        for (Constraint<TRSTerm> con : constrs) {
            if(qlpo.inRelation(con.getRight(), con.getLeft())) {
                return false;
            }
        }

        if (constrs.isEmpty()) {
            /* there are no more rules to check... */
            result = true;
            this.finalPrecedence = precedence.deepcopy();
        }
        else {
            /* take the first rule */
            Constraint<TRSTerm> c = (Constraint<TRSTerm>) constrs.remove(0);
            TRSTerm origL = c.getLeft();
            TRSTerm origR = c.getRight();

            if (QLPO.quasiEqual(origL, origR, precedence)) {
                /* (1) is not true -> check for strictness */
                if (c.getType()==OrderRelation.GR) {
                    result = false;
                }
                else {
                    result = this.QLPO(constrs, precedence);
                }
            }
            else if(c.getType()==OrderRelation.EQ) {
                /* maybe we can make the terms quasi-equal */

                ExtHashSetOfQosets<FunctionSymbol> equalizers = QLPO.minimalEqualizers(origL, origR, precedence, this.equiv);

                Iterator<Qoset<FunctionSymbol>> iqs = equalizers.iterator();

                while(iqs.hasNext() && result== false) {
                    Qoset<FunctionSymbol> precedenceClone = iqs.next();
                    List<Constraint<TRSTerm>> constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                    result = this.QLPO(constrsClone, precedenceClone);
                }
            }
            else if (origL.isVariable()) {
                if(!origR.isVariable() && c.getType()==OrderRelation.GE) {
                    TRSFunctionApplication r = (TRSFunctionApplication)origR;
                    FunctionSymbol rSymb =r.getRootSymbol();
                    if(rSymb.getArity()==0) {
                        /* minimal constants are GE to variables */
                        Qoset<FunctionSymbol> precedenceClone = precedence.deepcopy();
                        try {
                            precedenceClone.setMinimal(rSymb);
                            result = true;
                        }
                        catch(QosetException e) {
                            /* that didn't work... */
                        }
                        if(result) {
                            result = this.QLPO(constrs, precedenceClone);
                        }
                        else {
                            result = false;
                        }
                    }
                    else {
                        result = false;
                    }
                }
                else {
                    result = false;
                }
            }
            else {
                TRSFunctionApplication l = (TRSFunctionApplication)origL;
                /* l = f(l_1, ..., l_n) */
                if(origR.isVariable()) {
                    result = l.getVariables().contains(origR);
                }
                else {
                    TRSFunctionApplication r = (TRSFunctionApplication)origR;
                    /* r = g(r_1, ..., r_m) */
                    Iterator e1;
                    Iterator e2;
                    FunctionSymbol symbLeft = l.getRootSymbol();
                    FunctionSymbol symbRight = r.getRootSymbol();
                    TRSTerm newLeft;
                    TRSTerm newRight;
                    Qoset<FunctionSymbol> precedenceClone;
                    List<Constraint<TRSTerm>> constrsClone;

                    if(symbLeft.equals(symbRight) ||
                            precedence.areEquivalent(symbLeft, symbRight)) {
                        if(((FunctionSymbol)symbLeft).getArity()==1
                                &&((FunctionSymbol)symbRight).getArity()==1) {
                            /* monadic functions */
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(0, Constraint.create(l.getArgument(0),
                                    r.getArgument(0),
                                    OrderRelation.GR));
                            result = this.QLPO(constrsClone, precedence);
                        }
                        else {
                            /* this case must be handeled by (2b) */
                            e1 = l.getArguments().iterator();
                            e2 = r.getArguments().iterator();

                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);

                            ExtHashSetOfQosets<FunctionSymbol> equalizers;
                            Qoset<FunctionSymbol> prec;

                            int n = Math.min(((FunctionSymbol) symbLeft).getArity(),
                                    ((FunctionSymbol) symbRight).getArity());
                            int leftArity = ((FunctionSymbol) symbLeft).getArity();
                            int m = ((FunctionSymbol) symbRight).getArity();
                            equalizers = ExtHashSetOfQosets.create(this.signature);
                            equalizers.add(precedence.deepcopy());
                            int i=0;
                            int j;
                            while(i<n && result==false) {
                                j=i-1;
                                if(j>=0) {
                                    newLeft = l.getArgument(j);
                                    newRight = r.getArgument(j);
                                    try {
                                        prec = equalizers.intersectAll();
                                        equalizers = equalizers.mergeAll(QLPO.minimalGENGRs(newLeft, newRight, prec, this.equiv)).minimalElements();
                                    }
                                    catch(QosetException e) {
                                        /* nop */
                                    }
                                }
                                if(equalizers.size()!=0) {
                                    Iterator<Qoset<FunctionSymbol>> eqs = equalizers.iterator();
                                    while(eqs.hasNext() && result==false) {
                                        prec = eqs.next();
                                        newLeft = l.getArgument(i);
                                        newRight = r.getArgument(i);
                                        constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                                        constrsClone.add(0, Constraint.create(newLeft, newRight, OrderRelation.GR));
                                        for(j=i+1; j<m; j++) {
                                            newRight = r.getArgument(j);
                                            constrsClone.add(0, Constraint.create(l, newRight, OrderRelation.GR));
                                        }
                                        result = this.QLPO(constrsClone, prec);
                                    }
                                    i++;
                                }
                                else {
                                    /* stop it! */
                                    i=n;
                                }
                            }

                            if(result==false && m < leftArity) {
                                /* special case */
                                newLeft = l.getArgument(m-1);
                                newRight = r.getArgument(m-1);
                                try {
                                    prec = equalizers.intersectAll();
                                    equalizers = equalizers.mergeAll(QLPO.minimalGENGRs(newLeft, newRight, prec, this.equiv)).minimalElements();
                                }
                                catch(QosetException e) {
                                    /* nop */
                                }

                                if(equalizers.size()!=0) {
                                    Iterator<Qoset<FunctionSymbol>>eqs = equalizers.iterator();
                                    while(eqs.hasNext() && result==false) {
                                        prec = eqs.next();
                                        result = this.QLPO(constrs, prec);
                                    }
                                }
                            }

                            if(result==false) {
                                /* try partial non strict (2a) */
                                while(e1.hasNext() && result==false) {
                                    newLeft = (TRSTerm)e1.next();
                                    constrsClone =
                                        new ArrayList<Constraint<TRSTerm>>(constrs);
                                    constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                                    result = this.QLPO(constrsClone, precedence);
                                }
                            }
                        }
                    }
                    else if(precedence.isGreater(symbLeft, symbRight)) {
                        /* (2c), no need for (2a) */

                        e2 = r.getArguments().iterator();

                        constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);

                        while(e2.hasNext()) {
                            newRight = (TRSTerm) e2.next();
                            constrsClone.add(0, Constraint.create(l, newRight, OrderRelation.GR));
                        }

                        result = this.QLPO(constrsClone, precedence);
                    }
                    else if(precedence.isGreater(symbRight, symbLeft)) {
                        /* try non strict (2a) */
                        e1 = l.getArguments().iterator();

                        result = false;
                        while(e1.hasNext() && result==false) {
                            newLeft = (TRSTerm)e1.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                            result = this.QLPO(constrsClone, precedence);
                        }
                    }
                    else {
                        /* symbRightName and symbLeftName
                         * are incomparable
                         */
                        /* enrich the precedence by
                         * symbLeftName | symbRightName
                         * or symbLeftName ~ symbRightName
                         */
                        if(!precedence.isMinimal(symbLeft)) {
                            precedenceClone = precedence.deepcopy();
                            precedenceClone.setGreater(symbLeft, symbRight);
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);

                            constrsClone.add(0, c);

                            result = this.QLPO(constrsClone, precedenceClone);
                        }

                        if(result==false && (this.equiv==null || this.equiv.contains(Doubleton.create(symbLeft, symbRight)))) {
                            precedenceClone = precedence.deepcopy();
                            try {
                                precedenceClone.setEquivalent(symbLeft, symbRight);
                                constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                                constrsClone.add(0, c);
                                result = this.QLPO(constrsClone, precedenceClone);
                            }
                            catch(QosetException e) {
                                result = false;
                            }
                        }

                        if(result==false) {
                            /* changing the precedence didn't do, so
                             * let's try (2a)
                             */
                            e1 = l.getArguments().iterator();

                            result = false;
                            while(e1.hasNext() && result==false) {
                                newLeft = (TRSTerm)e1.next();
                                constrsClone =
                                    new ArrayList<Constraint<TRSTerm>>(constrs);
                                constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                                result = this.QLPO(constrsClone, precedence);
                            }
                        }
                    }

                    if(result==false && c.getType()==OrderRelation.GE) {
                        /* maybe we can make the terms quasi-equal
                         * or use x >= c
                         */

                        ExtHashSetOfQosets<FunctionSymbol> equalizers = QLPO.minimalGENGRs(l, r, precedence, this.equiv);

                        Iterator<Qoset<FunctionSymbol>> iqs = equalizers.iterator();

                        while(iqs.hasNext() && result== false) {
                            precedenceClone = iqs.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            result = this.QLPO(constrsClone, precedenceClone);
                        }
                    }
                }
            }
        }

        return result;
    }

}
