package aprove.verification.dpframework.Orders.Solvers ;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/** QLPOS-solver with full backtracking.
 * <p>
 * Starting from an specified initial or empty precedence and status map,
 * <code>QLPOSSolver</code> tries to solve the given constraints.
 * It'll extend the precedence and status map if necessary.
 *
 *   @author      Stephan Falke, Peter Schneider-Kamp
 *   @version $Id$
 */

public class QLPOSDepthSolver implements AbortableConstraintSolver<TRSTerm> {

    private List<Constraint<TRSTerm>> constrs;
    private List<FunctionSymbol> signature;
    private Qoset<FunctionSymbol> initialPrecedence;
    private StatusMap<FunctionSymbol> initialStatusMap;
    private Qoset<FunctionSymbol> finalPrecedence;
    private StatusMap<FunctionSymbol> finalStatusMap;
    private Collection<Doubleton<FunctionSymbol>> equiv;

    /* constructors */

    private QLPOSDepthSolver(List<FunctionSymbol> signature, Qoset<FunctionSymbol> initialPrecedence,
            StatusMap<FunctionSymbol> initialStatusMap, Collection<Doubleton<FunctionSymbol>> equiv) {
        this.signature = signature;
        this.initialPrecedence = initialPrecedence;
        this.initialStatusMap = initialStatusMap;
        this.equiv = equiv;
        this.finalPrecedence = null;
        this.finalStatusMap = null;
    }

    /** Creates a new instance of <code>QLPOSDepthSolver</code>.
     * @param signature   the names of the symbols
     */
    public static QLPOSDepthSolver create(Set<FunctionSymbol> signature) {
        return new QLPOSDepthSolver(new ArrayList<FunctionSymbol>(signature), null, null, null);
    }

    /** Creates a new instance of <code>QLPOSDepthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedence   the initial precedence
     * @param initialStatusMap   the initial status map
     */
    public static QLPOSDepthSolver create(Set<FunctionSymbol> signature,
            Qoset<FunctionSymbol> initialPrecedence,
            StatusMap<FunctionSymbol> initialStatusMap) {
        return new QLPOSDepthSolver(new ArrayList<FunctionSymbol>(signature),
                initialPrecedence, initialStatusMap, null);
    }

    /** Creates a new instance of <code>QLPOSDepthSolver</code>.
     * @param signature   the names of the symbols
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QLPOSDepthSolver create(Set<FunctionSymbol> signature, Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QLPOSDepthSolver(new ArrayList<FunctionSymbol>(signature), null, null, equiv);
    }

    /** Creates a new instance of <code>QLPOSDepthSolver</code>.
     * @param signature   the names of the symbols
     * @param initialPrecedence   the initial precedence
     * @param initialStatusMap   the initial status map
     * @param equiv          a collection of doubletons specifying which
     *                    function symbols may be equivalent
     */
    public static QLPOSDepthSolver create(Set<FunctionSymbol> signature,
            Qoset<FunctionSymbol> initialPrecedence,
            StatusMap<FunctionSymbol> initialStatusMap,
            Collection<Doubleton<FunctionSymbol>> equiv) {
        return new QLPOSDepthSolver(new ArrayList<FunctionSymbol>(signature),
                initialPrecedence, initialStatusMap, equiv);
    }

    /** Returns the final precedence, <code>null</code> if the constraints
     * can't be solved.
     */
    public Qoset<FunctionSymbol> getFinalPrecedence() {
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
            Qoset<FunctionSymbol> p = this.finalPrecedence.deepcopy();
            try {
                p.fix();
                return QLPOS.create(p, this.finalStatusMap);
            }
            catch(OrderedSetException e) {
                return null;
            }
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
     *                  (2b) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_n) and
     *                       there exists an 1<=i<=n such that
     *                       s_p(1) = t_p(1), ... ,s_p(i-1)=t_p(i-1),
     *                       s_p(i)>t_p(i) and s>t_p(j) for all i<j<=n, if
     *                       f has permutation p as status and f is equivalent
     *                       to g
     *                   or
     *                  (2c) s=f(s_1, ... ,s_n), t=g(t_1, ... ,t_m), f|g
     *                       and s>t_i for all 1<=i<=m
     * | is an partial order of the function symbols and is generated
     * 'on the fly' with this implementation.
     * p is a fixed permutation, for every n-ary f, of {1,...,n} which is
     * also generated 'on the fly'.
     */
    private boolean tryToOrder() {
        boolean result = true;
        this.finalPrecedence = null;
        this.finalStatusMap = null;
        Qoset<FunctionSymbol> precedence;
        StatusMap<FunctionSymbol> statusMap;

        if(this.initialPrecedence==null) {
            precedence = Qoset.create(this.signature);
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
            result = this.QLPOS(this.constrs, precedence, statusMap);
        }
        catch(OrderedSetException excp) {
            result = false;
        }

        return result;
    }

    private boolean QLPOS(List<Constraint<TRSTerm>> constrs, Qoset<FunctionSymbol> precedence,
            StatusMap<FunctionSymbol> statusMap) throws OrderedSetException {
        //    AProVETime.checkTimer();
        boolean result=false;

        QLPOS qlpos = QLPOS.create(precedence, statusMap);
        if(!constrs.isEmpty()) {
            /* remove constraints for which the current precedence
             * and statusmap suffices */
            List<Constraint<TRSTerm>> newConstrs = new ArrayList<Constraint<TRSTerm>>();
            for (Constraint<TRSTerm> con : constrs) {
                if(!qlpos.solves(con)) {
                    newConstrs.add(con);
                }
            }
            constrs = newConstrs;
        }

        /* check for reverse relation*/
        for (Constraint<TRSTerm> con : constrs) {
            if(qlpos.inRelation(con.getRight(), con.getLeft())) {
                return false;
            }
        }

        if (constrs.isEmpty()) {
            /* all constraints are satisfied! */
            result = true;
            this.finalPrecedence = precedence.deepcopy();
            this.finalStatusMap = statusMap.deepcopy();
        } else {
            /* take first constraint */
            Constraint<TRSTerm> c = (Constraint<TRSTerm>) constrs.remove(0);

            TRSTerm origL = c.getLeft();
            TRSTerm origR = c.getRight();

            if (QLPOS.quasiEqual(origL, origR, precedence, statusMap)) {
                /* (1) is not true -> check for strictness */
                if (c.getType()==OrderRelation.GR) {
                    result = false;
                } else {
                    result = this.QLPOS(constrs, precedence, statusMap);
                }
            }
            else if(c.getType()==OrderRelation.EQ) {
                /* maybe we can make the terms quasi-equal */

                ExtHashSetOfQuasiStatuses<FunctionSymbol> equalizers = QLPOS.minimalEqualizers(origL, origR, QuasiStatus.create(precedence, statusMap), this.equiv);

                Iterator<QuasiStatus<FunctionSymbol>> i = equalizers.iterator();

                while(i.hasNext() && result== false) {
                    QuasiStatus<FunctionSymbol> stat = i.next();
                    List<Constraint<TRSTerm>> constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                    result = this.QLPOS(constrsClone, stat.getPrecedence(), stat.getStatusMap());
                }
            }
            else if(origL.isVariable()) {
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
                            result = this.QLPOS(constrs, precedenceClone, statusMap);
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
                    StatusMap<FunctionSymbol> statusMapClone;
                    List<Constraint<TRSTerm>> constrsClone;

                    if (symbLeft.equals(symbRight) ||
                            precedence.areEquivalent(symbLeft, symbRight)) {
                        /* this case must be handeled by (2b) or (2d) */
                        if(((FunctionSymbol)symbLeft).getArity()==1
                                &&((FunctionSymbol)symbRight).getArity()==1) {
                            /* monadic functions don't need a status */
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(0, Constraint.create(l.getArgument(0),
                                    r.getArgument(0),
                                    OrderRelation.GR));
                            result = this.QLPOS(constrsClone, precedence, statusMap);
                        }
                        else {
                            /* we can try any permutation of the
                             * argument positions
                             */
                            boolean synEq = symbLeft.equals(symbRight);
                            List<Permutation> lefts = null;
                            List<Permutation> rights = null;
                            Iterable<Permutation> permsLeft;
                            Iterable<Permutation> permsRight;

                            int n = ((FunctionSymbol) symbLeft).getArity();
                            int m = ((FunctionSymbol) symbRight).getArity();

                            int min = Math.min(n, m);

                            if(statusMap.hasPermutation(symbLeft)) {
                                lefts = new ArrayList<Permutation>(1);
                                lefts.add(statusMap.getPermutation(symbLeft));
                                permsLeft = lefts;
                            }
                            else {
                                permsLeft = PermutationGenerator.create(n);
                            }

                            if(synEq || statusMap.hasPermutation(symbRight)) {
                                rights = new ArrayList<Permutation>();
                                if(statusMap.hasPermutation(symbRight)) {
                                    rights.add(statusMap.getPermutation(symbRight));
                                }
                            }

                            result = false;
                            for (Permutation pLeft : permsLeft) {
                                if (result) {
                                    break;
                                }

                                if(statusMap.hasPermutation(symbRight)) {
                                    permsRight = rights;
                                }
                                else if(synEq) {
                                    /* use the same permutation */
                                    rights.clear();
                                    rights.add(pLeft);
                                    permsRight = rights;
                                }
                                else {
                                    permsRight = PermutationGenerator.create(m);
                                }

                                for (Permutation pRight : permsRight) {
                                    if (result) {
                                        break;
                                    }

                                    statusMapClone = statusMap.deepcopy();
                                    statusMapClone.assignPermutation(symbLeft, pLeft);
                                    statusMapClone.assignPermutation(symbRight, pRight);

                                    QLPOS testqlpos = QLPOS.create(precedence,
                                            statusMapClone);
                                    if(testqlpos.inRelation(l, r)) {
                                        result = this.QLPOS(constrs, precedence, statusMapClone);
                                    }
                                    else {
                                        TRSFunctionApplication permL = LPOS.permuteTerm(l, pLeft);
                                        TRSFunctionApplication permR = LPOS.permuteTerm(r, pRight);
                                        e1 = permL.getArguments().iterator();
                                        e2 = permR.getArguments().iterator();

                                        ExtHashSetOfQuasiStatuses<FunctionSymbol> equalizers;
                                        QuasiStatus<FunctionSymbol> stat;
                                        Iterator<QuasiStatus<FunctionSymbol>> eq;

                                        equalizers = ExtHashSetOfQuasiStatuses.create(this.signature);
                                        equalizers.add(QuasiStatus.create(precedence, statusMapClone));
                                        int i=0;
                                        int j;
                                        while(i<min && result==false) {
                                            j=i-1;
                                            if(j>=0) {
                                                newLeft = permL.getArgument(j);
                                                newRight = permR.getArgument(j);
                                                try {
                                                    stat = equalizers.intersectAll();
                                                    equalizers = equalizers.mergeAll(QLPOS.minimalGENGRs(newLeft, newRight, stat, this.equiv));
                                                }
                                                catch(QuasiStatusException e) {
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
                                                    constrsClone.add(0, Constraint.create(newLeft, newRight, OrderRelation.GR));

                                                    for(j=i+1; j<m; j++) {
                                                        newRight = permR.getArgument(j);
                                                        constrsClone.add(0, Constraint.create(l, newRight, OrderRelation.GR));
                                                    }
                                                    result = this.QLPOS(constrsClone, stat.getPrecedence(), stat.getStatusMap());
                                                }
                                                i++;
                                            }
                                            else {
                                                /* stop it! */
                                                i=min;
                                            }
                                        }

                                        if(result==false && m < n) {
                                            /* special case */
                                            newLeft = permL.getArgument(m-1);
                                            newRight = permR.getArgument(m-1);
                                            try {
                                                stat = equalizers.intersectAll();
                                                equalizers = equalizers.mergeAll(QLPOS.minimalGENGRs(newLeft, newRight, stat, this.equiv)).minimalElements();
                                            }
                                            catch(QuasiStatusException e) {
                                                /* nop */
                                            }

                                            if(equalizers.size()!=0) {
                                                eq = equalizers.iterator();
                                                while(eq.hasNext() && result==false) {
                                                    stat = eq.next();
                                                    result = this.QLPOS(constrs, stat.getPrecedence(), stat.getStatusMap());
                                                }
                                            }
                                        }
                                    }
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
                                        result = this.QLPOS(constrsClone, precedence,
                                                statusMap);
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

                        result = this.QLPOS(constrsClone, precedence,
                                statusMap);
                    }
                    else if(precedence.isGreater(symbRight, symbLeft)) {
                        /* try non strict (2a) */
                        e1 = l.getArguments().iterator();

                        result = false;
                        while(e1.hasNext() && result==false) {
                            newLeft = (TRSTerm)e1.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            constrsClone.add(0, Constraint.create(newLeft, r, OrderRelation.GE));
                            result = this.QLPOS(constrsClone, precedence,
                                    statusMap);
                        }
                    }
                    else {
                        /* symbRightName and symbLeftName are
                         * incomparable
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

                            result = this.QLPOS(constrsClone, precedenceClone,
                                    statusMap);
                        }

                        if(result==false &&
                                (this.equiv==null || this.equiv.contains(Doubleton.create(symbLeft, symbRight)))) {
                            precedenceClone = precedence.deepcopy();
                            try {
                                precedenceClone.setEquivalent(symbLeft, symbRight);
                                constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                                constrsClone.add(0, c);
                                result = this.QLPOS(constrsClone, precedenceClone, statusMap);
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
                                result = this.QLPOS(constrsClone, precedence,
                                        statusMap);
                            }
                        }
                    }

                    if(result==false && c.getType()==OrderRelation.GE) {
                        /* maybe we can make the terms quasi-equal
                         * or can use x >= c
                         */

                        ExtHashSetOfQuasiStatuses<FunctionSymbol> equalizers = QLPOS.minimalGENGRs(l, r, QuasiStatus.create(precedence, statusMap), this.equiv);

                        Iterator<QuasiStatus<FunctionSymbol>> i = equalizers.iterator();

                        while(i.hasNext() && result== false) {
                            QuasiStatus<FunctionSymbol> stat = i.next();
                            constrsClone = new ArrayList<Constraint<TRSTerm>>(constrs);
                            result = this.QLPOS(constrsClone, stat.getPrecedence(), stat.getStatusMap());
                        }
                    }

                }
            }
        }

        return result;
    }

}
