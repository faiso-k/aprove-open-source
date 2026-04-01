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

/** RPO-solver with full backtracking.
 * <p>
 * Starting from an specified initial or empty precedence,
 * <code>RPOSolver</code> tries to solve the given constraints.
 * It'll extend the precedence if necessary.
 *
 *   @author      Stephan Falke
 *   @version $Id$
 */

public class RPODepthSolver implements AbortableConstraintSolver<TRSTerm> {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private Poset<FunctionSymbol> initialPrecedence;
    private Poset<FunctionSymbol> finalPrecedence;

    /* constructors */

    private RPODepthSolver(List<FunctionSymbol> signature, Poset<FunctionSymbol> initialPrecedence) {
        this.signature = signature;
        this.initialPrecedence = initialPrecedence;
        this.finalPrecedence = null;
    }

    /** Creates a new instance of <code>RPODepthSolver</code>.
     * @param signature   the names of the symbols
     */
    public static RPODepthSolver create(Set<FunctionSymbol> signature) {
        return new RPODepthSolver(new ArrayList<FunctionSymbol>(signature), null);
    }

    /** Creates a new instance of <code>RPODepthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedence   the initial precedence
     */
    public static RPODepthSolver create(Set<FunctionSymbol> signature,
            Poset<FunctionSymbol> initialPrecedence) {
        return new RPODepthSolver(new ArrayList<FunctionSymbol>(signature),
                initialPrecedence);
    }

    /** Returns the final precedence, <code>null</code> if the constraints
     * couldn't be solved.
     */
    public Poset<FunctionSymbol> getFinalPrecedence() {
        return this.finalPrecedence;
    }

    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            return RPO.create(this.finalPrecedence);
        }
        else {
            return null;
        }
    }


    /* return 'true' if the rules are ordered by the lexicographic path order,
     * return 'false' otherwise.
     * The recursive path order is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       {s_1, ... , s_n} >> {t_1, ... , t_n}
     *                       where >> is the multiset extension
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     * Terms are considered equal if they differ only in a permutation of
     * their arguments.
     * | is an partial order of the function symbols and is generated
     * 'on the fly' with this implementation.
     */
    private boolean tryToOrder() {
        boolean result = true;
        this.finalPrecedence = null;
        Poset<FunctionSymbol> precedence;

        if(this.initialPrecedence==null) {
            precedence = Poset.create(this.signature);
        }
        else {
            precedence = this.initialPrecedence.deepcopy();
        }

        try {
            result = this.RPO(this.constrs, precedence, new HashSet<Constraint<TRSTerm>>());
        }
        catch (OrderedSetException excp) {
            result = false;
        }

        return result;
    }

    private boolean RPO(List<Constraint<TRSTerm>> constrs,
            Poset<FunctionSymbol> precedence, HashSet<Constraint<TRSTerm>> checkNeeded) throws OrderedSetException {
        //    AProVETime.checkTimer();
        boolean result=false;

        RPO rpo = RPO.create(precedence);
        if(!constrs.isEmpty()) {
            /* remove constraints for which the current precedence suffices */
            List<Constraint<TRSTerm>> newConstrs = new ArrayList<Constraint<TRSTerm>>();
            for (Constraint<TRSTerm> con : constrs) {
                if(!rpo.solves(con)) {
                    newConstrs.add(con);
                }
            }
            constrs = newConstrs;
        }

        /* check for reverse relation*/
        for (Constraint<TRSTerm> con : constrs) {
            if(rpo.inRelation(con.getRight(), con.getLeft())) {
                return false;
            }
        }

        if (constrs.isEmpty()) {
            /* there are no more rules to check... */
            /* but are all delayed checks satisfied? */
            Iterator<Constraint<TRSTerm>> i = checkNeeded.iterator();
            while(i.hasNext()) {
                if(!rpo.solves(i.next())) {
                    return false;
                }
            }
            result = true;
            this.finalPrecedence = precedence.deepcopy();
        }
        else {
            /* take the first rule */
            Constraint<TRSTerm> c = (Constraint<TRSTerm>) constrs.remove(0);
            TRSTerm origL = c.getLeft();
            TRSTerm origR = c.getRight();

            if (Multiterm.create(origL).equals(Multiterm.create(origR))) {
                /* (1) is not true -> check for strictness */
                if (c.getType()==OrderRelation.GR) {
                    result = false;
                }
                else {
                    result = this.RPO(constrs, precedence, checkNeeded);
                }
            }
            else if(c.getType()==OrderRelation.EQ) {
                return false;
            }
            else if (origL.isVariable()) {
                if(!origR.isVariable() && c.getType()==OrderRelation.GE) {
                    TRSFunctionApplication r = (TRSFunctionApplication)origR;
                    FunctionSymbol rSymb = r.getRootSymbol();
                    if(rSymb.getArity()==0) {
                        /* minimal constants are GE to variables */
                        Poset<FunctionSymbol> precedenceClone = precedence.deepcopy();
                        try {
                            precedenceClone.setMinimal(rSymb);
                            result = true;
                        }
                        catch(PosetException e) {
                            /* that didn't work... */
                        }
                        if(result) {
                            result = this.RPO(constrs, precedenceClone, checkNeeded);
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
                    Poset<FunctionSymbol> precedenceClone;
                    List<Constraint<TRSTerm>> constrsClone;

                    if(symbLeft.equals(symbRight)) {
                        if(((FunctionSymbol)symbLeft).getArity()==1) {
                            /* monadic functions */
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(0, Constraint.create(l.getArgument(0),
                                    r.getArgument(0),
                                    OrderRelation.GR));
                            result = this.RPO(constrsClone, precedence, checkNeeded);
                        }
                        else {
                            /* case (2b) */
                            MultiSet<TRSTerm> argL = new HashMultiSet<TRSTerm>(l.getArguments());
                            MultiSet<TRSTerm> argR = new HashMultiSet<TRSTerm>(r.getArguments());
                            MultisetExtension mul = MultisetExtension.create(rpo);

                            OrderRelation tmpRes = mul.relate(argL, argR);
                            if(tmpRes==OrderRelation.GR) {
                                /* current precedence suffices */
                                result = this.RPO(constrs, precedence, checkNeeded);
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

                                    result = this.RPO(constrsClone, precedence, checkNeededClone);

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

                        result = this.RPO(constrsClone, precedence, checkNeeded);
                    }
                    else if(precedence.isGreater(symbRight, symbLeft)) {
                        /* try non strict (2a) */
                        e1 = l.getArguments().iterator();

                        result = false;
                        while(e1.hasNext() && result==false) {
                            newLeft = (TRSTerm)e1.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                            result = this.RPO(constrsClone, precedence, checkNeeded);
                        }
                    }
                    else {
                        /* symbRightName and symbLeftName
                         * are incomparable
                         */
                        /* enrich the precedence by
                         * symbLeftNamy | symbRightName
                         */
                        precedenceClone = precedence.deepcopy();
                        precedenceClone.setGreater(symbLeft, symbRight);
                        constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);

                        constrsClone.add(0, c);

                        result = this.RPO(constrsClone, precedenceClone, checkNeeded);

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
                                result = this.RPO(constrsClone, precedence, checkNeeded);
                            }
                        }
                    }

                    if(result==false && c.getType()==OrderRelation.GE) {
                        /* maybe we can use x >= c
                         */

                        ExtHashSetOfPosets<FunctionSymbol> equalizers = RPO.minimalGENGRs(l, r, precedence);

                        Iterator<Poset<FunctionSymbol>> ips = equalizers.iterator();

                        while(ips.hasNext() && result== false) {
                            precedenceClone = ips.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            result = this.RPO(constrsClone, precedenceClone, checkNeeded);
                        }
                    }
                }
            }
        }

        return result;
    }

}
