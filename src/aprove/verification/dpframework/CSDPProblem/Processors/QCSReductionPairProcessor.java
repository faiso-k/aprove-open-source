package aprove.verification.dpframework.CSDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.dpframework.CSDPProblem.Solvers.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class QCSReductionPairProcessor
        extends QCSDPProcessor {

    private final SolverFactory factory;

    private final boolean allStrict;

    @ParamsViaArgumentObject
    public QCSReductionPairProcessor(Arguments arguments) {
        this.factory = arguments.order;
        this.allStrict = arguments.allStrict;
    }

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem obl) {
        return true;
    }

    @Override
    public Result processQCSDP(QCSDPProblem problem, Abortion aborter)
            throws AbortionException {
        Set<Rule> usableRules = problem.getUsableRules();

        Map<Rule, QActiveCondition> active = QUsableRules
                .getRulesAsConditionMap(usableRules);

        QActiveSolver solver = this.factory.getQActiveSolver();

        // ugly.
        if (solver instanceof QCSDPNegCoeffPoloSolver) {
            QCSDPNegCoeffPoloSolver csSolver = (QCSDPNegCoeffPoloSolver) solver;
            csSolver.setMu(problem.getReplacementMap());
        }

        QActiveOrder order = solver.solveQActive(problem.getDp(), active, false,
                this.allStrict, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful();
        }

        return this.getResult(problem, order);
    }

    private Result getResult(QCSDPProblem problem, QActiveOrder order)
            throws AbortionException {

        Set<Rule> keptPairs = new LinkedHashSet<Rule>();
        Set<Rule> deletedPairs = new LinkedHashSet<Rule>();

        for (Rule l_to_r : problem.getDp()) {
            if (order.solves(Constraint.fromRule(l_to_r, OrderRelation.GR))) {
                deletedPairs.add(l_to_r);
            } else {
                keptPairs.add(l_to_r);
            }
        }

        if (Globals.useAssertions) {
            // check that all usable rules are oriented weakly
            for (Rule s_to_t : problem.getUsableRules()) {
                assert (order.solves(Constraint.fromRule(s_to_t, OrderRelation.GE)));
            }

            // check that all pairs are oriented weakly
            for (Rule s_to_t : problem.getDp()) {
                assert (order.solves(Constraint.fromRule(s_to_t, OrderRelation.GE)));
            }

            // check that at least one rule was oriented strictly
            assert (!deletedPairs.isEmpty());
        }

        if (deletedPairs.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        QCSDPProblem todo = QCSDPProblem.create(ImmutableCreator
                .create(keptPairs), problem);

        return ResultFactory.proved(todo, YNMImplication.EQUIVALENT,
                new QCSReductionPairProof(keptPairs, deletedPairs, order));
    }

    private class QCSReductionPairProof
            extends Proof.DefaultProof {
        private final Set<Rule> keptPairs;

        private final Set<Rule> deletedPairs;

        private final QActiveOrder order;

        QCSReductionPairProof(Set<Rule> keptPairs, Set<Rule> deletedPairs,
                QActiveOrder order) {
            this.order = order;
            this.keptPairs = keptPairs;
            this.deletedPairs = deletedPairs;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();

            if (this.keptPairs.isEmpty()) {
                s.append(o.export("All"));
            } else {
                s.append(o.export("Some"));
            }

            s.append(o.export(" dependency pairs could be ordered "
                    + "strictly and thus be deleted by the "
                    + "context-sensitive reduction pair processor")
                    + o.cite(Citation.DA_EMMES)
                    + o.export(". The order used was:") + o.cond_linebreak());
            s.append(this.order.export(o));
            s.append(o.export("These pairs could be deleted:")
                    + o.cond_linebreak());
            s.append(o.set(this.deletedPairs, Export_Util.RULES));

            return s.toString();
        }
    }

    public static class Arguments {
        public SolverFactory order;
        public boolean allStrict = false;
    }
}
