package aprove.verification.dpframework.Orders.Solvers ;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.Multiterm;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** QRPO-solver with full backtracking.
 * <p>
 * Starting from an specified initial or empty precedence and status map,
 * <code>QRPOSolver</code> tries to solve the given constraints.
 * It'll extend the precedence and status map if necessary.
 *
 *   @author      Stephan Falke, Peter Schneider-Kamp
 *   @version $Id$
 */

public class QRPODepthSolver implements AbortableConstraintSolver<TRSTerm> {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private Qoset<FunctionSymbol> initialPrecedence;
    private Qoset<FunctionSymbol> finalPrecedence;
    private Collection<Doubleton<FunctionSymbol>> equiv;

    /* constructors */

    private QRPODepthSolver(List<FunctionSymbol> signature, Qoset<FunctionSymbol> initialPrecedence, Collection<Doubleton<FunctionSymbol>> equiv) {
        this.signature = signature;
        this.initialPrecedence = initialPrecedence;
        this.equiv = equiv;
        this.finalPrecedence = null;
    }

    /** Creates a new instance of <code>QRPODepthSolver</code>.
     * @param signature   the names of the symbols
     */
    public static QRPODepthSolver create(Set<FunctionSymbol> signature) {
        return new QRPODepthSolver(new ArrayList<FunctionSymbol>(signature), null, null);
    }

    /** Creates a new instance of <code>QRPODepthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedence   the initial precedence
     */
    public static QRPODepthSolver create(Set<FunctionSymbol> signature, Qoset<FunctionSymbol> initialPrecedence) {
        return new QRPODepthSolver(new ArrayList<FunctionSymbol>(signature), initialPrecedence, null);
    }

    /** Creates a new instance of <code>QRPODepthSolver</code>.
     * @param signature   the names of the symbols
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QRPODepthSolver create(Set<FunctionSymbol> signature, Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QRPODepthSolver(new ArrayList<FunctionSymbol>(signature), null, equiv);
    }

    /** Creates a new instance of <code>QRPODepthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedence   the initial precedence
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QRPODepthSolver create(Set<FunctionSymbol> signature, Qoset<FunctionSymbol> initialPrecedence, Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QRPODepthSolver(new ArrayList<FunctionSymbol>(signature), initialPrecedence, equiv);
    }

    /** Returns the final precedence, <code>null</code> if the constraints
     * can't be solved.
     */
    public Qoset getFinalPrecedence() {
        return this.finalPrecedence;
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
        Qoset<FunctionSymbol> precedence;

        if(this.initialPrecedence==null) {
            precedence = Qoset.create(this.signature);
        }
        else {
            precedence = this.initialPrecedence.deepcopy();
        }

        try {
            result = this.QRPO(this.constrs, precedence, new HashSet<Constraint<TRSTerm>>());
        }
        catch(OrderedSetException excp) {
            result = false;
        }

        return result;
    }

    private boolean QRPO(List<Constraint<TRSTerm>> constrs, Qoset<FunctionSymbol> precedence, HashSet<Constraint<TRSTerm>> checkNeeded)
    throws OrderedSetException {
        //    AProVETime.checkTimer();
        boolean result=false;

        QRPO qrpo = QRPO.create(precedence);
        if(!constrs.isEmpty()) {
            /* remove constraints for which the current precedence
             * and statusmap suffices or which are already ordered by EMB*/
            List<Constraint<TRSTerm>> newConstrs = new ArrayList<Constraint<TRSTerm>>();
            for (Constraint<TRSTerm> con : constrs) {
                if(!qrpo.solves(con)) {
                    newConstrs.add(con);
                }
            }
            constrs = newConstrs;
        }

        /* check for reverse relation*/
        for (Constraint<TRSTerm> con : constrs) {
            if(qrpo.inRelation(con.getRight(), con.getLeft())) {
                return false;
            }
        }

        if (constrs.isEmpty()) {
            /* all constraints are satisfied! */
            /* but are all delayed checks satisfied? */
            Iterator<Constraint<TRSTerm>> i = checkNeeded.iterator();
            while(i.hasNext()) {
                if(!qrpo.solves(i.next())) {
                    return false;
                }
            }
            result = true;
            this.finalPrecedence = precedence.deepcopy();
        } else {
            /* take first constraint */
            Constraint<TRSTerm> c = (Constraint<TRSTerm>) constrs.remove(0);

            TRSTerm origL = c.getLeft();
            TRSTerm origR = c.getRight();

            if (Multiterm.create(origL, precedence).equals(Multiterm.create(origR, precedence))) {
                /* (1) is not true -> check for strictness */
                if (c.getType()==OrderRelation.GR) {
                    result = false;
                } else {
                    result = this.QRPO(constrs, precedence, checkNeeded);
                }
            }
            else if(c.getType()==OrderRelation.EQ) {
                /* maybe we can 'equalize' the terms by changing
                 * equivalences of function symbols.
                 */

                ExtHashSetOfQosets<FunctionSymbol> equalizers = QRPO.minimalEqualizers(origL, origR, precedence, this.equiv);

                Iterator<Qoset<FunctionSymbol>> i = equalizers.iterator();

                while(i.hasNext() && result== false) {
                    Qoset<FunctionSymbol> precedenceClone = i.next();
                    List<Constraint<TRSTerm>> constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                    result = this.QRPO(constrsClone, precedenceClone, checkNeeded);
                }
            }
            else if (origL.isVariable()) {
                if(!origR.isVariable() && c.getType()==OrderRelation.GE) {
                    TRSFunctionApplication r = (TRSFunctionApplication)origR;
                    FunctionSymbol rSymb = r.getRootSymbol();
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
                            result = this.QRPO(constrs, precedenceClone, checkNeeded);
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

                    result = false;

                    Iterator e1;
                    Iterator e2;
                    FunctionSymbol symbLeft = l.getRootSymbol();
                    FunctionSymbol symbRight = r.getRootSymbol();
                    TRSTerm newLeft;
                    TRSTerm newRight;
                    Qoset<FunctionSymbol> precedenceClone;
                    List<Constraint<TRSTerm>> constrsClone;

                    if (symbLeft.equals(symbRight)
                            || precedence.areEquivalent(symbLeft, symbRight)) {
                        /* this case must be handeled by (2b) */
                        if(((FunctionSymbol)symbLeft).getArity()==1
                                &&((FunctionSymbol)symbRight).getArity()==1) {
                            /* monadic functions don't need a status */
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(0, Constraint.create(l.getArgument(0),
                                    r.getArgument(0),
                                    OrderRelation.GR));
                            result = this.QRPO(constrsClone, precedence, checkNeeded);
                        }
                        else {
                            /* (2b) */
                            MultiSet<TRSTerm> argL = new HashMultiSet<TRSTerm>(l.getArguments());
                            MultiSet<TRSTerm> argR = new HashMultiSet<TRSTerm>(r.getArguments());
                            MultisetExtension mul = MultisetExtension.create(qrpo);

                            OrderRelation tmpRes = mul.relate(argL, argR);
                            if(tmpRes==OrderRelation.GR) {
                                /* current precedence suffice */
                                result = this.QRPO(constrs, precedence, checkNeeded);
                            }
                            else {
                                MultiSet<TRSTerm> L = mul.getLeft();
                                MultiSet<TRSTerm> R = mul.getRight();

                                List<TRSTerm> LVector = L.toList();
                                List<TRSTerm> RVector = R.toList();

                                int sizeL = LVector.size();
                                int sizeR = RVector.size();

                                int i;
                                for (Sequence s : SequenceGenerator.create(sizeR, sizeL)) {
                                    if (result) {
                                        break;
                                    }
                                    constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);

                                    for(i=0; i<sizeR; i++) {
                                        constrsClone.add(0,
                                                Constraint.create(LVector.get(s.get(i)),
                                                        RVector.get(i),
                                                        OrderRelation.GE));
                                    }

                                    HashSet<Constraint<TRSTerm>> checkNeededClone = new HashSet<Constraint<TRSTerm>>(checkNeeded);

                                    checkNeededClone.add(c);

                                    result = this.QRPO(constrsClone, precedence, checkNeededClone);

                                }
                            }
                        }
                    }
                    else if(precedence.isGreater(symbLeft, symbRight)) {
                        /* (2c) */

                        e2 = r.getArguments().iterator();
                        constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);

                        while (e2.hasNext()) {
                            newRight = (TRSTerm) e2.next();
                            constrsClone.add(0, Constraint.create(l, newRight, OrderRelation.GR));
                        }

                        result = this.QRPO(constrsClone, precedence, checkNeeded);
                    }
                    else if(precedence.isGreater(symbRight, symbLeft)) {
                        /* try non strict (2a) */
                        e1 = l.getArguments().iterator();

                        result = false;
                        while(e1.hasNext() && result==false) {
                            newLeft = (TRSTerm)e1.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                            result = this.QRPO(constrsClone, precedence, checkNeeded);
                        }
                    }
                    else {
                        /* symbRight and symbLeft are
                         * incomparable
                         */
                        if(!precedence.isMinimal(symbLeft)) {
                            precedenceClone = precedence.deepcopy();
                            precedenceClone.setGreater(symbLeft, symbRight);
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);

                            constrsClone.add(0, c);

                            result = this.QRPO(constrsClone, precedenceClone, checkNeeded);
                        }

                        /* equivalent? */
                        if(result==false &&
                                (this.equiv==null || this.equiv.contains(Doubleton.create(symbLeft, symbRight)))) {
                            precedenceClone = precedence.deepcopy();
                            try {
                                precedenceClone.setEquivalent(symbLeft, symbRight);
                                constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                                constrsClone.add(0, c);
                                result = this.QRPO(constrsClone, precedenceClone, checkNeeded);
                            }
                            catch(QosetException e) {
                                result = false;
                            }
                        }

                        if(result==false) {
                            /* try non strict (2a) */
                            e1 = l.getArguments().iterator();

                            result = false;
                            while(e1.hasNext() && result==false) {
                                newLeft = (TRSTerm)e1.next();
                                constrsClone =
                                    new ArrayList<Constraint<TRSTerm>>(constrs);
                                constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                                result = this.QRPO(constrsClone, precedence, checkNeeded);
                            }
                        }
                    }

                    if(result==false && c.getType()==OrderRelation.GE) {
                        /* maybe we can 'equalize' the terms by changing
                         * equivalences of function symbols or
                         * we can use x >= c
                         */

                        ExtHashSetOfQosets<FunctionSymbol> equalizers = QRPO.minimalGENGRs(l, r, precedence, this.equiv);

                        Iterator<Qoset<FunctionSymbol>> i = equalizers.iterator();

                        while(i.hasNext() && result== false) {
                            precedenceClone = i.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            result = this.QRPO(constrsClone, precedenceClone, checkNeeded);
                        }
                    }
                }
            }
        }

        return result;
    }

}
