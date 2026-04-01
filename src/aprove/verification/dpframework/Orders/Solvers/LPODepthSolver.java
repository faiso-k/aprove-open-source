package aprove.verification.dpframework.Orders.Solvers;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/** LPO-solver with full backtracking.
 * <p>
 * Starting from an specified initial or empty precedence,
 * </code>LPOSolver</code> tries to solve the given constraints.
 * It'll extend the precedence if necessary.
 *
 *   @author      Stephan Falke, Peter Schneider-Kamp
 *   @version $Id$
 */

public class LPODepthSolver implements AbortableConstraintSolver<TRSTerm> {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private Poset<FunctionSymbol> initialPrecedence;
    private Poset<FunctionSymbol> finalPrecedence;

    /* constructors */

    private LPODepthSolver(List<FunctionSymbol> signature, Poset<FunctionSymbol> initialPrecedence) {
        this.signature = signature;
        this.initialPrecedence = initialPrecedence;
        this.finalPrecedence = null;
    }

    /** Creates a new instance of <code>LPOSolver</code>.
     * @param signature   the names of the symbols
     */
    public static LPODepthSolver create(Set<FunctionSymbol> signature) {
        return new LPODepthSolver(new ArrayList<FunctionSymbol>(signature), null);
    }

    /** Creates a new instance of <code>LPOSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedence   the initial precedence
     */
    public static LPODepthSolver create(Set<FunctionSymbol> signature,
            Poset<FunctionSymbol> initialPrecedence) {
        return new LPODepthSolver(new ArrayList<FunctionSymbol>(signature),
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

        // reverse list
        int size = cs.size();
        size -= 1;
        int i = 0;
        while (i < size) {
            Constraint<TRSTerm> tmp = this.constrs.set(i, this.constrs.get(size));
            this.constrs.set(size, tmp);
            i++;
            size--;
        }

        if(this.tryToOrder()) {
            return LPO.create(this.finalPrecedence);
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
     *   | is an partial order of the function symbols and is generated
     *   'on the fly' with this implementation.
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
            result = this.LPO(this.constrs, precedence);
        }
        catch (OrderedSetException excp) {
            result = false;
        }
        return result;
    }


    private boolean LPO(List<Constraint<TRSTerm>> constrs,
            Poset<FunctionSymbol> precedence) throws OrderedSetException {
        boolean result=false;


        LPO lpo = LPO.create(precedence);
        if(!constrs.isEmpty()) {
            /* remove constraints for which the current precedence suffices */
            List<Constraint<TRSTerm>> newConstrs = new ArrayList<Constraint<TRSTerm>>();
            for (Constraint<TRSTerm> con : constrs) {
                if(!lpo.solves(con)) {
                    newConstrs.add(con);
                }
            }
            constrs = newConstrs;
        }
        if(!constrs.isEmpty()) {
            /* check for reverse relation*/
            int n = constrs.size();
            Constraint<TRSTerm> con;
            while (n > 0) {
                n--;
                con = constrs.get(n);
                if(lpo.inRelation(con.getRight(), con.getLeft())) {
                    return false;
                }
            }
        }

        if (constrs.isEmpty()) {
            /* there are no more rules to check... */
            result = true;
            this.finalPrecedence = precedence.deepcopy();
        }
        else {
            /* take the first rule */
            Constraint<TRSTerm> c = constrs.remove(constrs.size()-1);
            TRSTerm origL = c.getLeft();
            TRSTerm origR = c.getRight();

            if (origL.equals(origR)) {
                /* (1) is not true -> check for strictness */
                if (c.getType()==OrderRelation.GR) {
                    result = false;
                }
                else {
                    result = this.LPO(constrs, precedence);
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
                            result = this.LPO(constrs, precedenceClone);
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
                /* l = f(l_1, ..., l_n) */
                if(origR.isVariable()) {
                    result = origL.getVariables().contains(origR);
                }
                else {
                    TRSFunctionApplication r = (TRSFunctionApplication)origR;
                    TRSFunctionApplication l = (TRSFunctionApplication)origL;
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
                            constrsClone.add(Constraint.create(l.getArgument(0),
                                    r.getArgument(0),
                                    OrderRelation.GR));
                            result = this.LPO(constrsClone, precedence);
                        }
                        else {
                            /* this case must be handeled by (2b) */
                            e1 = l.getArguments().iterator();
                            e2 = r.getArguments().iterator();

                            ExtHashSetOfPosets<FunctionSymbol> equalizers;
                            Poset<FunctionSymbol> prec;
                            Iterator<Poset<FunctionSymbol>> eq;

                            int n = ((FunctionSymbol) symbLeft).getArity();
                            equalizers = ExtHashSetOfPosets.create(this.signature);
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
                                        equalizers = equalizers.mergeAll(LPO.minimalGENGRs(newLeft, newRight, prec)).minimalElements();
                                    }
                                    catch(PosetException e) {
                                        /* nop */
                                    }
                                }
                                if(equalizers.size()!=0) {
                                    eq = equalizers.iterator();
                                    while(eq.hasNext() && result==false) {
                                        prec = eq.next();
                                        newLeft = l.getArgument(i);
                                        newRight = r.getArgument(i);
                                        constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                                        Constraint<TRSTerm> newConstr = Constraint.create(newLeft, newRight, OrderRelation.GR);
                                        for(j=i+1; j<n; j++) {
                                            newRight = r.getArgument(j);
                                            constrsClone.add(Constraint.create(l, newRight, OrderRelation.GR));
                                        }
                                        constrsClone.add(newConstr);
                                        result = this.LPO(constrsClone, prec);
                                    }
                                    i++;
                                }
                                else {
                                    /* stop it! */
                                    i=n;
                                }
                            }

                            if(result==false) {
                                /* try partial non strict (2a) */
                                while(e1.hasNext() && result==false) {
                                    newLeft = (TRSTerm)e1.next();
                                    constrsClone =
                                        new ArrayList<Constraint<TRSTerm>>(constrs);
                                    constrsClone.add(Constraint.create(newLeft, r, OrderRelation.GE));
                                    result = this.LPO(constrsClone, precedence);
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
                            constrsClone.add(
                                    Constraint.create(l, newRight, OrderRelation.GR));

                        }

                        result = this.LPO(constrsClone, precedence);
                    }
                    else if(precedence.isGreater(symbRight, symbLeft)) {
                        /* try non strict (2a) */
                        e1 = l.getArguments().iterator();

                        result = false;
                        while(e1.hasNext() && result==false) {
                            newLeft = (TRSTerm)e1.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(Constraint.create(newLeft, r, OrderRelation.GE));
                            result = this.LPO(constrsClone, precedence);
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

                        constrsClone.add(c);

                        result = this.LPO(constrsClone, precedenceClone);

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
                                constrsClone.add(Constraint.create(newLeft, r, OrderRelation.GE));
                                result = this.LPO(constrsClone, precedence);
                            }
                        }
                    }

                    if(result==false && c.getType()==OrderRelation.GE) {
                        /* maybe we satisify it with the x >= c extension */

                        ExtHashSetOfPosets<FunctionSymbol> equalizers = LPO.minimalGENGRs(l, r, precedence);

                        Iterator<Poset<FunctionSymbol>> i = equalizers.iterator();

                        while(i.hasNext() && result== false) {
                            precedenceClone = i.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            result = this.LPO(constrsClone, precedenceClone);
                        }
                    }
                }
            }
        }

        return result;
    }

}
