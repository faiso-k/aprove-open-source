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

/** RPOS-solver with full backtracking.
 * <p>
 * Starting from an specified initial or empty precedence and status map,
 * <code>RPOSSolver</code> tries to solve the given constraints.
 * It'll extend the precedence and status map if necessary.
 *
 *   @author      Stephan Falke, Peter Schneider-Kamp
 *   @version $Id$
 */

public class RPOSDepthSolver implements AbortableConstraintSolver<TRSTerm> {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private Poset<FunctionSymbol> initialPrecedence;
    private StatusMap<FunctionSymbol> initialStatusMap;
    private Poset<FunctionSymbol> finalPrecedence;
    private StatusMap<FunctionSymbol> finalStatusMap;

    /* constructors */

    private RPOSDepthSolver(List<FunctionSymbol> signature, Poset<FunctionSymbol> initialPrecedence,
            StatusMap<FunctionSymbol> initialStatusMap) {
        this.signature = signature;
        this.initialPrecedence = initialPrecedence;
        this.initialStatusMap = initialStatusMap;
        this.finalPrecedence = null;
        this.finalStatusMap = null;
    }

    /** Creates a new instance of <code>RPOSDepthSolver</code>.
     * @param signature   the names of the symbols
     */
    public static RPOSDepthSolver create(Set<FunctionSymbol> signature) {
        return new RPOSDepthSolver(new ArrayList<FunctionSymbol>(signature), null, null);
    }

    /** Creates a new instance of <code>RPOSDepthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedence   the initial precedence
     * @param initialStatusMap   the initial status map
     */
    public static RPOSDepthSolver create(Set<FunctionSymbol> signature,
            Poset<FunctionSymbol> initialPrecedence,
            StatusMap<FunctionSymbol> initialStatusMap) {
        return new RPOSDepthSolver(new ArrayList<FunctionSymbol>(signature),
                initialPrecedence, initialStatusMap);
    }

    /** Returns the final precedence, <code>null</code> if the constraints
     * can't be solved.
     */
    public Poset<FunctionSymbol> getFinalPrecedence() {
        return this.finalPrecedence;
    }

    /** Returns the final status map, <code>null</code> if the constraints
     * can't be solved.
     */
    public StatusMap<FunctionSymbol> getFinalStatusMap() {
        return this.finalStatusMap;
    }

    @Override
    public ExportableOrder<TRSTerm> solve(Collection<Constraint<TRSTerm>> cs, Abortion aborter) {
        this.constrs = new ArrayList<Constraint<TRSTerm>>(cs);

        if(this.tryToOrder()) {
            return RPOS.create(this.finalPrecedence, this.finalStatusMap);
        }
        else {
            return null;
        }
    }


    /* return 'true' if the rules are ordered by the lexicographic path order
     * with status, return 'false' otherwise.
     * The lexicographic path order with status is defined by
     *   s>t  iff  (1) not s=t
     *              and (2a) s=f(s_1, ... ,s_n) and s_j>=t for some 1<=j<=n
     *                   or
     *                  (2b) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       there exists an 1<=i<=n such that
     *                       s_p(1) = t_p(1), ... ,s_p(i-1)=t_p(i-1),
     *                       s_p(i)>t_p(i) and s>t_p(j) for all i<j<=n, if
     *                       f has permutation p as status
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     *                   or
     *                  (2d) s=f(s_1, ... ,s_n), t=f(t_1, ... ,t_n) and
     *                       {s_1, ... , s_n} >> {t_1, ... , t_n}
     *                       where >> is the multiset extension, if
     *                       f has multiset status
     * Terms are considered equal their multiterms according to the status map
     * are equal.
     * | is an partial order of the function symbols and is generated
     * 'on the fly' with this implementation.
     * p is a fixed permutation, for every n-ary f, of {1,...,n} which is
     * also generated 'on the fly'.
     */
    private boolean tryToOrder() {
        boolean result = true;
        this.finalPrecedence = null;
        this.finalStatusMap = null;
        Poset<FunctionSymbol> precedence;
        StatusMap<FunctionSymbol> statusMap;

        if(this.initialPrecedence==null) {
            precedence = Poset.create(this.signature);
        }
        else {
            precedence = this.initialPrecedence.deepcopy();
        }
        if(this.initialStatusMap==null) {
            statusMap = StatusMap.create(this.signature);
        }
        else {
            statusMap = this.initialStatusMap.deepcopy();
        }

        try {
            result = this.RPOS(this.constrs, precedence, statusMap, new HashSet<Constraint<TRSTerm>>());
        }
        catch(OrderedSetException excp) {
            result = false;
        }

        return result;
    }

    private boolean RPOS(List<Constraint<TRSTerm>> constrs, Poset<FunctionSymbol> precedence,
            StatusMap<FunctionSymbol> statusMap, HashSet<Constraint<TRSTerm>> checkNeeded) throws OrderedSetException {
        //    AProVETime.checkTimer();
        boolean result=false;

        RPOS rpos = RPOS.create(precedence, statusMap);
        if(!constrs.isEmpty()) {
            /* remove constraints for which the current precedence
             * and statusmap suffices */
            List<Constraint<TRSTerm>> newConstrs = new ArrayList<Constraint<TRSTerm>>();
            for (Constraint<TRSTerm> con : constrs) {
                if(!rpos.solves(con)) {
                    newConstrs.add(con);
                }
            }
            constrs = newConstrs;
        }

        /* check for reverse relation*/
        for (Constraint<TRSTerm> con : constrs) {
            if(rpos.inRelation(con.getRight(), con.getLeft())) {
                return false;
            }
        }

        if (constrs.isEmpty()) {
            /* all constraints are satisfied! */
            /* but are all delayed checks satisfied? */
            Iterator<Constraint<TRSTerm>> i = checkNeeded.iterator();
            while(i.hasNext()) {
                if(!rpos.solves(i.next())) {
                    return false;
                }
            }
            result = true;
            this.finalPrecedence = precedence.deepcopy();
            this.finalStatusMap = statusMap.deepcopy();
        } else {
            /* take first constraint */
            Constraint<TRSTerm> c = (Constraint<TRSTerm>) constrs.remove(0);

            TRSTerm origL = c.getLeft();
            TRSTerm origR = c.getRight();

            if (Multiterm.create(origL, statusMap).equals(Multiterm.create(origR, statusMap))) {
                /* (1) is not true -> check for strictness */
                if (c.getType()==OrderRelation.GR) {
                    result = false;
                } else {
                    /* GR or EQ */
                    result = this.RPOS(constrs, precedence, statusMap, checkNeeded);
                }
            }
            else if(c.getType()==OrderRelation.EQ) {
                /* maybe we can 'equalize' the terms by assigning
                 * multiset status to some function symbols that
                 * don't have a status yet
                 */

                Status<FunctionSymbol> stat = Status.create(precedence, statusMap);
                ExtHashSetOfStatuses<FunctionSymbol> equalizers = RPOS.minimalEqualizers(origL, origR, stat);

                Iterator<Status<FunctionSymbol>> i = equalizers.iterator();
                while(i.hasNext() && result==false) {
                    stat = i.next();
                    List<Constraint<TRSTerm>> constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                    result = this.RPOS(constrsClone, stat.getPrecedence(), stat.getStatusMap(), checkNeeded);
                }
            }
            else if(origL.isVariable()) {
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
                            result = this.RPOS(constrs, precedenceClone, statusMap, checkNeeded);
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
                    Poset<FunctionSymbol> precedenceClone;
                    StatusMap<FunctionSymbol> statusMapClone;
                    List<Constraint<TRSTerm>> constrsClone;

                    if (symbLeft.equals(symbRight)) {
                        /* this case must be handeled by (2b) or (2d) */
                        if(((FunctionSymbol)symbLeft).getArity()==1) {
                            /* monadic functions don't need a status */
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(0, Constraint.create(l.getArgument(0),
                                    r.getArgument(0),
                                    OrderRelation.GR));
                            result = this.RPOS(constrsClone, precedence, statusMap, checkNeeded);
                        }
                        else {
                            if(statusMap.hasMultisetStatus(symbLeft)) {
                                /* (2d) */
                                MultiSet<TRSTerm> argL = new HashMultiSet<TRSTerm>(l.getArguments());
                                MultiSet<TRSTerm> argR = new HashMultiSet<TRSTerm>(r.getArguments());
                                MultisetExtension mul = MultisetExtension.create(rpos);

                                OrderRelation tmpRes = mul.relate(argL, argR);
                                if(tmpRes==OrderRelation.GR) {
                                    /* current precedence and status map suffice */
                                    result = this.RPOS(constrs, precedence, statusMap, checkNeeded);
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

                                        constrsClone =  new ArrayList<Constraint<TRSTerm>>(constrs);

                                        for(i=0; i<sizeR; i++) {
                                            constrsClone.add(0,
                                                    Constraint.create((TRSTerm)LVector.get(s.get(i)),
                                                            (TRSTerm)RVector.get(i),
                                                            OrderRelation.GE));
                                        }

                                        HashSet<Constraint<TRSTerm>> checkNeededClone = new HashSet<Constraint<TRSTerm>>(checkNeeded);

                                        checkNeededClone.add(c);

                                        result = this.RPOS(constrsClone, precedence, statusMap, checkNeededClone);

                                    }
                                }
                            }
                            else if(statusMap.hasPermutation(symbLeft)) {
                                /* we have to use the given permutation */

                                Permutation p =
                                    statusMap.getPermutation(symbLeft);
                                TRSFunctionApplication permL = LPOS.permuteTerm(l, p);
                                TRSFunctionApplication permR = LPOS.permuteTerm(r, p);
                                int n=((FunctionSymbol)symbLeft).getArity();

                                ExtHashSetOfStatuses<FunctionSymbol> equalizers;
                                Status<FunctionSymbol> stat;
                                Iterator<Status<FunctionSymbol>> eq;

                                equalizers = ExtHashSetOfStatuses.create(this.signature);
                                equalizers.add(Status.create(precedence, statusMap));
                                int i=0;
                                int j;
                                while(i<n && result==false) {
                                    j=i-1;
                                    if(j>=0) {
                                        newLeft = permL.getArgument(j);
                                        newRight = permR.getArgument(j);
                                        try {
                                            stat = equalizers.intersectAll();
                                            equalizers = equalizers.mergeAll(RPOS.minimalGENGRs(newLeft, newRight, stat));
                                        }
                                        catch(StatusException e) {
                                            /* nop */
                                        }
                                    }
                                    if(equalizers.size()!=0) {
                                        eq = equalizers.iterator();
                                        while(eq.hasNext() && result==false) {
                                            stat = eq.next();
                                            newLeft = permL.getArgument(i);
                                            newRight = permR.getArgument(i);

                                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);

                                            Constraint<TRSTerm> newConstr = Constraint.create(newLeft, newRight, OrderRelation.GR);
                                            for(j=i+1; j<n; j++) {
                                                newRight = permR.getArgument(j);
                                                constrsClone.add(0, Constraint.create(l, newRight, OrderRelation.GR));
                                            }

                                            constrsClone.add(0, newConstr);
                                            result = this.RPOS(constrsClone, stat.getPrecedence(), stat.getStatusMap(), checkNeeded);
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
                                    e1 = permL.getArguments().iterator();
                                    while(e1.hasNext() && result==false) {
                                        newLeft = (TRSTerm)e1.next();
                                        constrsClone =
                                            new ArrayList<Constraint<TRSTerm>>(constrs);
                                        constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                                        result = this.RPOS(constrsClone, precedence,
                                                statusMap, checkNeeded);
                                    }
                                }
                            }
                            else {
                                /* we can try any permutation of the
                                 * argument positions, and also multiset status
                                 */
                                int n = ((FunctionSymbol) symbLeft).getArity();
                                Iterator<Permutation> perm = PermutationGenerator.create(n).iterator();
                                Permutation p;

                                result = false;
                                while(perm.hasNext() && result==false) {
                                    p = perm.next();
                                    TRSFunctionApplication permL = LPOS.permuteTerm(l, p);
                                    TRSFunctionApplication permR = LPOS.permuteTerm(r, p);
                                    e1 = permL.getArguments().iterator();
                                    e2 = permR.getArguments().iterator();

                                    statusMapClone = statusMap.deepcopy();
                                    statusMapClone.assignPermutation(symbLeft, p);

                                    ExtHashSetOfStatuses<FunctionSymbol> equalizers;
                                    Status<FunctionSymbol> stat;
                                    Iterator<Status<FunctionSymbol>> eq;

                                    equalizers = ExtHashSetOfStatuses.create(this.signature);
                                    equalizers.add(Status.create(precedence,
                                            statusMapClone));
                                    int i=0;
                                    int j;
                                    while(i<n && result==false) {
                                        j=i-1;
                                        if(j>=0) {
                                            newLeft = permL.getArgument(j);
                                            newRight = permR.getArgument(j);
                                            try {
                                                stat = equalizers.intersectAll();
                                                equalizers = equalizers.mergeAll(RPOS.minimalGENGRs(newLeft, newRight, stat));
                                            }
                                            catch(StatusException e) {
                                                /* nop */
                                            }
                                        }
                                        if(equalizers.size()!=0) {
                                            eq = equalizers.iterator();
                                            while(eq.hasNext() && result==false) {
                                                stat = eq.next();
                                                newLeft = permL.getArgument(i);
                                                newRight = permR.getArgument(i);

                                                constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);

                                                Constraint<TRSTerm> newConstr = Constraint.create(newLeft, newRight, OrderRelation.GR);
                                                for(j=i+1; j<n; j++) {
                                                    newRight = permR.getArgument(j);
                                                    constrsClone.add(0, Constraint.create(l, newRight, OrderRelation.GR));
                                                }

                                                constrsClone.add(0, newConstr);
                                                result = this.RPOS(constrsClone, stat.getPrecedence(), stat.getStatusMap(), checkNeeded);
                                            }
                                            i++;
                                        }
                                        else {
                                            /* stop it! */
                                            i=n;
                                        }
                                    }
                                }

                                if(result==false) {
                                    /* multiset status? */
                                    constrsClone =
                                        new ArrayList<Constraint<TRSTerm>>(constrs);

                                    constrsClone.add(0, c);

                                    statusMapClone = statusMap.deepcopy();
                                    statusMapClone.assignMultisetStatus(symbLeft);
                                    result = this.RPOS(constrsClone, precedence,
                                            statusMapClone, checkNeeded);
                                }

                                if(result==false) {
                                    /* try (2a) */
                                    e1 = l.getArguments().iterator();

                                    while(e1.hasNext() && result==false) {
                                        newLeft = (TRSTerm)e1.next();
                                        constrsClone =
                                            new ArrayList<Constraint<TRSTerm>>(constrs);
                                        /* non strict! */
                                        constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                                        result = this.RPOS(constrsClone, precedence,
                                                statusMap, checkNeeded);
                                    }
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

                        result = this.RPOS(constrsClone, precedence,
                                statusMap, checkNeeded);
                    }
                    else if(precedence.isGreater(symbRight, symbLeft)) {
                        /* try non strict (2a) */
                        e1 = l.getArguments().iterator();

                        result = false;
                        while(e1.hasNext() && result==false) {
                            newLeft = (TRSTerm)e1.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                            result = this.RPOS(constrsClone, precedence,
                                    statusMap, checkNeeded);
                        }
                    }
                    else {
                        /* symbRightName and symbLeftName are
                         * incomparable
                         */
                        precedenceClone = precedence.deepcopy();
                        precedenceClone.setGreater(symbLeft, symbRight);
                        constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);

                        constrsClone.add(0, c);

                        result = this.RPOS(constrsClone, precedenceClone,
                                statusMap, checkNeeded);

                        if(result==false) {
                            /* try non strict (2a) */
                            e1 = l.getArguments().iterator();

                            result = false;
                            while(e1.hasNext() && result==false) {
                                newLeft = (TRSTerm)e1.next();
                                constrsClone =
                                    new ArrayList<Constraint<TRSTerm>>(constrs);
                                constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                                result = this.RPOS(constrsClone, precedence,
                                        statusMap, checkNeeded);
                            }
                        }
                    }

                    if(result==false && c.getType()==OrderRelation.GE) {
                        /* maybe we can 'equalize' the terms by assigning
                         * multiset status to some function symbols that
                         * don't have a status yet or we can use x >= c
                         */

                        Status<FunctionSymbol> stat = Status.create(precedence, statusMap);
                        ExtHashSetOfStatuses<FunctionSymbol> equalizers = RPOS.minimalGENGRs(l, r, stat);

                        Iterator<Status<FunctionSymbol>> i = equalizers.iterator();
                        while(i.hasNext() && result==false) {
                            stat = i.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            result = this.RPOS(constrsClone, stat.getPrecedence(), stat.getStatusMap(), checkNeeded);
                        }
                    }
                }
            }
        }

        return result;
    }

}
