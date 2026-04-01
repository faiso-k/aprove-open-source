package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.AFSPrecalculation.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class QDPAfsOrderSolver implements QActiveSolver {

    private int restriction;
    private SolverFactory factory;

    public QDPAfsOrderSolver(SolverFactory factory, /*ExtendedAfsFilter filter,*/ int restriction) {
        this.restriction = restriction;
        this.factory = factory;
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R, boolean active, boolean allstrict, Abortion aborter) throws AbortionException {
        Set<Pair<Set<Pair<TRSTerm,TRSTerm>>,Set<Pair<TRSTerm,TRSTerm>>>> filtered2afs = new LinkedHashSet<>();
//        AbortableIterator<Pair<Map<FunctionSymbol, YNM[]>, Set<Rule>>> it = aTransQDP.getAfsIterable(this.restriction, this.active).iterator();
        AbortableIterator<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>> it = QDPAfsOrderSolver.getAfsIterable(P, R.keySet(), this.restriction, active).iterator();
        while (it.hasNext(aborter)) {
            Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>> solution = it.next(aborter);
            Set<Afs> afss = Afs.extendYNMMap(solution.x);
//          System.out.println("After M-extension: "+afss.size());
            afss = QDPAfsOrderSolver.applyFilter(/*this.filter,*/ afss);
//          System.out.println("After collapse-extension: "+afss.size());
            for (Afs afs : afss) {
                aborter.checkAbortion();
                Set<Pair<TRSTerm,TRSTerm>> fP = afs.filter(P);
                Set<Pair<TRSTerm,TRSTerm>> fR = new LinkedHashSet<>();
                for (Map.Entry<? extends GeneralizedRule, QActiveCondition> entry : R.entrySet()) {
                    if (entry.getValue().specialize(afs) == QActiveCondition.TRUE) {
                        fR.add(afs.filter(entry.getKey()));
                    }
                }
//                Set<Pair<Term,Term>> fR = afs.filter(solution.y);
                Pair<Set<Pair<TRSTerm,TRSTerm>>,Set<Pair<TRSTerm,TRSTerm>>> PR = new Pair<>(fP,fR);
                if (!filtered2afs.contains(PR)) {
                    filtered2afs.add(PR);
                    ExportableOrder<TRSTerm> order = this.solve(fP,fR,allstrict,aborter);
//                  System.out.println("afs = "+afs);
//                  System.out.println("PR = "+PR);
                    if (order != null) {
                        return new AfsOrder(afs, order);
                    }
                }
            }
        }
        return null;
    }

    private ExportableOrder<TRSTerm> solve(Set<Pair<TRSTerm,TRSTerm>> P, Set<Pair<TRSTerm,TRSTerm>> R, boolean allstrict, Abortion aborter) throws AbortionException {
        Set<Constraint<TRSTerm>> rulecs = Constraint.fromPairsOfTerms(R, OrderRelation.GE);
        Set<Constraint<TRSTerm>> cs = Constraint.fromPairsOfTerms(P, OrderRelation.GR);
        cs.addAll(rulecs);
        AbortableConstraintSolver<TRSTerm> solver = this.factory.getSolver(cs);
        if (allstrict) {
            return solver.solve(cs, aborter);
        } else {
            for (Pair<TRSTerm,TRSTerm> strictdp : P) {
                aborter.checkAbortion();
                cs = new LinkedHashSet<Constraint<TRSTerm>>();
                cs.add(Constraint.create(strictdp.x, strictdp.y, OrderRelation.GR));
                cs.addAll(rulecs);
                for (Pair<TRSTerm,TRSTerm> dp : P) {
                    if (dp != strictdp) {
                        cs.add(Constraint.create(dp.x, dp.y, OrderRelation.GE));
                    }
                }
                ExportableOrder<TRSTerm> order = solver.solve(cs, aborter);
                if (order != null) {
                    return order;
                }
            }
        }
        return null;
    }

    private static Set<Afs> applyFilter(Set<Afs> afss) {
        Set<Afs> newAfss = new LinkedHashSet<Afs>();
        for (Afs afs : afss) {
            newAfss.addAll(QDPAfsOrderSolver.getFilters(afs));
        }
        return newAfss;
    }

    private static Set<Afs> getFilters(Afs afs) {
        List<FunctionSymbol> fs = new Vector<FunctionSymbol>(afs.getFunctionSymbols());
        return Afs.extendWithCollapsing(afs, fs);
    }

    /**
     * returns a set of all possible AFSs that lead to active usable rules which
     * form a TRS. Note that all AFSs will be stored, i.e. if it is clear that these
     * AFSs will no longer be needed, one should forget these AFSs by calling
     * <code>forgetAfsIterable</code>
     * @param restriction - a limit of arguments per function symbol, -1 means no limit.
     */
    private static AbortableIterable<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>> getAfsIterable(Set<? extends GeneralizedRule> P, Set<? extends GeneralizedRule> R, int restriction, boolean active) {
        return new DynamicYnmPEVLSolver(P, R, restriction, false, active);
    }

}
