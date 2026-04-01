package aprove.verification.dpframework.Orders.Solvers ;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/** QEMB-solver with full backtracking.
 * <p>
 * Starting from an specified initial or empty precedence,
 * </code>QEMBolver</code> tries to solve the given constraints.
 * It'll extend the precedence if necessary.
 *
 *   @author      Stephan Falke, Peter Schneider-Kamp
 *   @version $Id$
 */

public class QEMBDepthSolver implements AbortableConstraintSolver<TRSTerm> {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private Qoset<FunctionSymbol> initialPrecedence;
    private Qoset<FunctionSymbol> finalPrecedence;
    private Collection<Doubleton<FunctionSymbol>> equiv;

    /* constructors */

    private QEMBDepthSolver(List<FunctionSymbol> signature, Qoset<FunctionSymbol> initialPrecedence, Collection<Doubleton<FunctionSymbol>> equiv) {
        this.signature = signature;
        this.initialPrecedence = initialPrecedence;
        this.equiv = equiv;
        this.finalPrecedence = null;
    }

    /** Creates a new instance of <code>QEMBDepthSolver</code>.
     * @param signature   the names of the symbols
     */
    public static QEMBDepthSolver create(Set<FunctionSymbol> signature) {
        return new QEMBDepthSolver(new ArrayList<FunctionSymbol>(signature), null, null);
    }

    /** Creates a new instance of <code>QEMBDepthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedence   the initial precedence
     */
    public static QEMBDepthSolver create(Set<FunctionSymbol> signature,
            Qoset<FunctionSymbol> initialPrecedence) {
        return new QEMBDepthSolver(new ArrayList<FunctionSymbol>(signature),
                initialPrecedence, null);
    }
    /** Creates a new instance of <code>QEMBDepthSolver</code>.
     * @param signature   the names of the symbols
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QEMBDepthSolver create(Set<FunctionSymbol> signature, Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QEMBDepthSolver(new ArrayList<FunctionSymbol>(signature), null, equiv);
    }

    /** Creates a new instance of <code>QEMBDepthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedence   the initial precedence
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QEMBDepthSolver create(Set<FunctionSymbol> signature,
            Qoset<FunctionSymbol> initialPrecedence,
            Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QEMBDepthSolver(new ArrayList<FunctionSymbol>(signature),
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
            return QEMB.create(this.finalPrecedence);
        }
        else {
            return null;
        }
    }

    /* return 'true' if term t is homeomorphicly embedded in term t,
     * return 'false' otherwise.
     * The homeomorphic embedding is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_n) and
     *                       s_1>=t_1, ... , s_n>=t_n where f and g are
     *                       equivalent
     *
     * the equivalences are generated 'on-the-fly'
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
            result = this.QEMB(this.constrs, precedence);
        }
        catch (QosetException excp) {
            result = false;
        }

        return result;
    }

    private boolean QEMB(List<Constraint<TRSTerm>> constrs,
            Qoset<FunctionSymbol> precedence) throws QosetException {
        //   AProVETime.checkTimer();
        boolean result=false;

        QEMB qemb = QEMB.create(precedence);
        if(!constrs.isEmpty()) {
            /* remove constraints for which the current precedence suffices */
            List<Constraint<TRSTerm>> newConstrs = new ArrayList<Constraint<TRSTerm>>();
            for (Constraint<TRSTerm> con : constrs) {
                if(!qemb.solves(con)) {
                    newConstrs.add(con);
                }
            }
            constrs = newConstrs;
        }

        /* check for reverse relation*/
        for (Constraint<TRSTerm> con : constrs) {
            if(qemb.inRelation(con.getRight(), con.getLeft())) {
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
                    result = this.QEMB(constrs, precedence);
                }
            }
            else if(c.getType()==OrderRelation.EQ) {
                /* maybe we can make the terms quasi-equal */

                ExtHashSetOfQosets<FunctionSymbol> equalizers = QLPO.minimalEqualizers(origL, origR, precedence, this.equiv);

                Iterator<Qoset<FunctionSymbol>> iqs = equalizers.iterator();

                while(iqs.hasNext() && result== false) {
                    Qoset<FunctionSymbol> precedenceClone = iqs.next();
                    List<Constraint<TRSTerm>> constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                    result = this.QEMB(constrsClone, precedenceClone);
                }
            }
            else if (origL.isVariable()) {
                result = false;
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

                        /* this case must be handeled by (2b) */
                        e1 = l.getArguments().iterator();
                        e2 = r.getArguments().iterator();

                        constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);

                        while(e1.hasNext()) {
                            newLeft = (TRSTerm)e1.next();
                            newRight = (TRSTerm)e2.next();

                            constrsClone.add(0,Constraint.create(newLeft, newRight, OrderRelation.GE));
                        }

                        result = this.QEMB(constrsClone, precedence);

                        if(result==true) {
                            if(QLPO.quasiEqual(l, r, this.finalPrecedence)) {
                                /* we did too much! */
                                result = false;
                                this.finalPrecedence = null;
                            }
                        }

                        e1 = l.getArguments().iterator();
                        if(result==false) {
                            /* try non strict (2a) */
                            while(e1.hasNext() && result==false) {
                                newLeft = (TRSTerm)e1.next();
                                constrsClone =
                                    new ArrayList<Constraint<TRSTerm>>(constrs);
                                constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                                result = this.QEMB(constrsClone, precedence);
                            }
                        }
                    }
                    else {
                        /* symbRightName and symbLeftName
                         * are not equal and not equivalent
                         */
                        /* add equivalence of symbRightName and symbLeftName */

                        if(symbLeft.getArity()==symbRight.getArity() &&
                                (this.equiv==null || this.equiv.contains(Doubleton.create(symbLeft, symbRight)))) {
                            precedenceClone = precedence.deepcopy();
                            precedenceClone.setEquivalent(symbLeft, symbRight);
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(0, c);
                            result = this.QEMB(constrsClone, precedenceClone);
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
                                result = this.QEMB(constrsClone, precedence);
                            }
                        }
                    }

                    if(result==false && c.getType()==OrderRelation.GE) {
                        /* maybe we can make the terms quasi-equal */

                        ExtHashSetOfQosets<FunctionSymbol> equalizers = QLPO.minimalEqualizers(l, r, precedence, this.equiv);

                        Iterator<Qoset<FunctionSymbol>> iqs = equalizers.iterator();

                        while(iqs.hasNext() && result== false) {
                            precedenceClone = iqs.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            result = this.QEMB(constrsClone, precedenceClone);
                        }
                    }
                }
            }
        }

        return result;
    }

}
