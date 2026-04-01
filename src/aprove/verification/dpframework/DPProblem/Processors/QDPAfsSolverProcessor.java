package aprove.verification.dpframework.DPProblem.Processors;

import static aprove.verification.dpframework.BasicStructures.Utility.SimpleStrictMode.*;

import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @deprecated use ReductionPairProcessor and QDPPOSolver instead!
 */
@Deprecated
public class QDPAfsSolverProcessor extends QDPProblemProcessor {

    private final int restriction;
    private final Afs initial;
    private final SolverFactory factory;
    private final SimpleStrictMode strictMode;
    private final Set<Rule> strictDPs;
    private final boolean active;

    public QDPAfsSolverProcessor(SolverFactory factory,
            SimpleStrictMode strictMode,
            int restriction,
            boolean active) {
        this.restriction = restriction;
        this.factory = factory;
        this.strictMode = strictMode;
        this.initial = null;
        this.strictDPs = null;
        this.active = active;
    }

    @ParamsViaArgumentObject
    public QDPAfsSolverProcessor(Arguments arguments) {
        this(arguments.factory, SEARCHSTRICT, 2, arguments.active);
    }

    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter)
    throws AbortionException {


        ImmutableSet<Rule> dps = qdp.getP();

        Set<Pair<Set<Pair<TRSTerm,TRSTerm>>,Set<Pair<TRSTerm,TRSTerm>>>> filtered2afs = new LinkedHashSet<Pair<Set<Pair<TRSTerm,TRSTerm>>,Set<Pair<TRSTerm,TRSTerm>>>>();
        AbortableIterator<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>> it = qdp.getAfsIterable(this.restriction, this.active).iterator();
        while (it.hasNext(aborter)) {
            Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>> solution = it.next(aborter);
            Set<Afs> afss = Afs.extendYNMMap(solution.x);
//          System.out.println("After M-extension: "+afss.size());
            afss = QDPAfsSolverProcessor.applyFilter(afss);
//          System.out.println("After collapse-extension: "+afss.size());
            for (Afs afs : afss) {
                if (this.initial != null) {
//                    afs = this.initial.merge(afs);
                    if (afs == null) {
                        continue;
                    }
                }
                aborter.checkAbortion();
                Set<Pair<TRSTerm,TRSTerm>> P = afs.filter(dps);
                Set<Pair<TRSTerm,TRSTerm>> R = afs.filter(solution.y);
                Pair<Set<Pair<TRSTerm,TRSTerm>>,Set<Pair<TRSTerm,TRSTerm>>> PR = new Pair<Set<Pair<TRSTerm,TRSTerm>>,Set<Pair<TRSTerm,TRSTerm>>>(P,R);
                if (!filtered2afs.contains(PR)) {
                    filtered2afs.add(PR);
                    ExportableOrder<TRSTerm> order = this.solve(P,R,aborter);
//                  System.out.println("afs = "+afs);
//                  System.out.println("PR = "+PR);
                    if (order != null) {

                        order = new AfsOrder(afs, order);

                        Set<Rule> usableRules = qdp.getQUsableRulesCalculator().getUsableRules(dps, afs);

                        return QDPReductionPairProcessor.getResult(order,
                                usableRules, qdp, null);
                    }
                }
            }
        }
        return ResultFactory.unsuccessful();
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        // The reason for requiring minimality or innermost is that the AFSIterable always takes usable rules.
        // moreover, the a-transformation also uses always usable rules. (see POLO for how to use a-transformation with all rules)
        return qdp.getMinimal() || qdp.QsupersetOfLhsR();
    }

    private ExportableOrder<TRSTerm> solve(Set<Pair<TRSTerm,TRSTerm>> P, Set<Pair<TRSTerm,TRSTerm>> R, Abortion aborter) throws AbortionException {
        Set<Constraint<TRSTerm>> rulecs = Constraint.fromPairsOfTerms(R, OrderRelation.GE);
        Set<Constraint<TRSTerm>> cs = Constraint.fromPairsOfTerms(P, OrderRelation.GR);
        cs.addAll(rulecs);
        AbortableConstraintSolver<TRSTerm> solver = this.factory.getSolver(cs);
        if (this.strictMode == ALLSTRICT || P.size() == 1) {
            return solver.solve(cs, aborter);
        } else {
            for (Pair<TRSTerm,TRSTerm> strictdp : P) {
                if (this.strictDPs != null && !this.strictDPs.contains(strictdp)) {
                    continue;
                }
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
            newAfss.addAll(QDPAfsSolverProcessor.getFilters(afs));
        }
        return newAfss;
    }

    private static Set<Afs> getFilters(Afs afs) {
        List<FunctionSymbol> fs = new Vector<FunctionSymbol>(afs.getFunctionSymbols());
        return Afs.extendWithCollapsing(afs, fs);
    }


    public static class Arguments {
        public boolean active;
        public SolverFactory factory = new LPOFactory(new LPOFactory.Arguments());
    }

}
