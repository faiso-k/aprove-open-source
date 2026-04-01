package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Util.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import immutables.*;

/**
 * Multi RRR processor. Lets up to 8 solver run in parallel and search for different orderings
 * satisfying the RRR constraints. All orderings found within the grace time will be merged in
 * the following way: The MultiRRR processor deletes every rule, that is oriented strictly by
 * at least one ordering and keeps every rule, that is only oriented non-strictly by every
 * ordering.
 *
 * @author Andreas Kelle-Emden
 */
public class QTRSMultiRRRProcessor extends QTRSProcessor
        implements MultiProcessor<QTRSProblem, QTRSMultiRRRProcessor.SubResult> {

    static class SubResult {
        public final Set<Rule> deletedRules;
        public final ExportableOrder<TRSTerm> order;

        public SubResult(Set<Rule> deletedRules, ExportableOrder<TRSTerm> order) {
            this.deletedRules = deletedRules;
            this.order = order;
        }
    }

    public static class Arguments {
        public int deadline = Integer.MAX_VALUE;
        public int gracetime = Integer.MAX_VALUE;

        // Workaround until our strategy language supports lists
        public SolverFactory order1;
        public SolverFactory order2;
        public SolverFactory order3 = null;
        public SolverFactory order4 = null;
        public SolverFactory order5 = null;
        public SolverFactory order6 = null;
        public SolverFactory order7 = null;
        public SolverFactory order8 = null;
    }

    final int deadline;
    final int gracetime;
    final List<SolverFactory> solvers;

    @ParamsViaArgumentObject
    public QTRSMultiRRRProcessor(Arguments args) {
        this.deadline = args.deadline;
        this.gracetime = args.gracetime;
        this.solvers = new ArrayList<SolverFactory>();
        if (args.order1 == null || args.order2 == null) {
            throw new IllegalArgumentException("Need at least 2 solvers!");
        }
        this.solvers.add(args.order1);
        this.solvers.add(args.order2);
        if (args.order3 != null) {
            this.solvers.add(args.order3);
        }
        if (args.order4 != null) {
            this.solvers.add(args.order4);
        }
        if (args.order5 != null) {
            this.solvers.add(args.order5);
        }
        if (args.order6 != null) {
            this.solvers.add(args.order6);
        }
        if (args.order7 != null) {
            this.solvers.add(args.order7);
        }
        if (args.order8 != null) {
            this.solvers.add(args.order8);
        }
    }

    @Override
    public SubResult processSub(int index, QTRSProblem qtrs, Abortion aborter) throws AbortionException {

        Set<Rule> R = qtrs.getR();
        RRRSolver solver = this.solvers.get(index).getRRRSolver();
        if (!solver.isRRRApplicable(R)) {
            return null;
        }

        Set<Rule> deletedRules = new LinkedHashSet<Rule>();
        if (Globals.useAssertions) {
            assert(!R.isEmpty());
        }
        aborter.checkAbortion();

        ExportableOrder<TRSTerm> order = solver.solveRRR(R, aborter);
        if (order == null) {
            return null;
        }

        // Collect removed rules
        for (Rule rule : R) {
            aborter.checkAbortion();
            if (order.inRelation(rule.getLeft(), rule.getRight())) {
                deletedRules.add(rule);
            } else {
                Constraint<TRSTerm> cons = Constraint.create(rule.getLeft(), rule.getRight(), OrderRelation.GE);
                if (Globals.useAssertions) {
                    assert(order.solves(cons));
                }
                if (!order.solves(cons)) {
                    return null;
                }
            }
        }

        return new SubResult(deletedRules, order);
    }

    @Override
    public Result merge(QTRSProblem qtrs, List<SubResult> subResults, Abortion aborter) throws AbortionException {
        Set<Rule> allDeletedRules = new LinkedHashSet<Rule>();
        Set<Rule> remainingRules = new LinkedHashSet<Rule>(qtrs.getR());
        List<ExportableOrder<TRSTerm>> orders = new ArrayList<ExportableOrder<TRSTerm>>(subResults.size());
        for(SubResult subResult: subResults) {
            allDeletedRules.addAll(subResult.deletedRules);
            remainingRules.removeAll(subResult.deletedRules);
            orders.add(subResult.order);
        }
        if (allDeletedRules.size() == 0) {
            return ResultFactory.unsuccessful();
        }

        // Produce Proof and stuff here.

        ImmutableSet<Rule> newSubProblemRules;
        newSubProblemRules = ImmutableCreator.create(remainingRules);
        QTRSProblem newQtrs;
        newQtrs = qtrs.createSubProblem(newSubProblemRules);
        Proof proof = new QTRSMultiRRRProof(allDeletedRules, orders);

        Result result = ResultFactory.proved(newQtrs, YNMImplication.EQUIVALENT, proof);
        return result;

    }

    @Override
    protected Result processQTRS(QTRSProblem qtrs, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        MultiProcessorHelper<QTRSProblem, SubResult> helper;
        helper = new MultiProcessorHelper<QTRSProblem, SubResult>(this, this.solvers.size());
        helper.setDeadline(this.deadline);
        helper.setGracetime(this.gracetime);
        return helper.process(qtrs, aborter);
    }

    @Override
    public boolean isQTRSApplicable(QTRSProblem qtrs) {
        return true;
    }

    @Override
    public String getName() {
        return "Multi-RRR Processor";
    }


    private static class QTRSMultiRRRProof extends Proof {

        private Set<Rule> deletedRules;
        private final List<ExportableOrder<TRSTerm>> orders;

        private QTRSMultiRRRProof(Set<Rule> deletedRules, List<ExportableOrder<TRSTerm>> orders) {
            this.deletedRules = deletedRules;
            this.orders = orders;
        }

        @Override
        public String export(Export_Util o) {
            StringBuilder result;
            result = new StringBuilder();
            result.append("We used the following orderings:");
            for (ExportableOrder<TRSTerm> order : this.orders) {
                result.append(o.linebreak());
                result.append(o.export(order));
            }
            result.append("With these orderings the following rules can be removed by the rule removal processor "+o.cite(Citation.LPAR04)+ " because they are oriented strictly:");
            result.append(o.linebreak());
            result.append(o.set(this.deletedRules, Export_Util.RULES));
            result.append(o.newline());
            result.append(o.linebreak());
            return result.toString();
        }

    }

}
