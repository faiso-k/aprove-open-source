package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class RelRRProcessor extends RelTRSProcessor {

    private final SolverFactory factory;

    @ParamsViaArguments("Order")
    public RelRRProcessor(SolverFactory order) {
        this.factory = order;
    }

    @Override
    public Result processRelTRS(RelTRSProblem problem, Abortion aborter, RuntimeInformation rti) throws AbortionException {

        Set<Rule> R = problem.getR();
        Set<Rule> S = problem.getS();
        Set<Rule> RandS = new LinkedHashSet<Rule>(R);
        RandS.addAll(S);

        RRRSolver solver = this.factory.getRRRSolver();
        if (!(solver.isRRRApplicable(R) && solver.isRRRApplicable(S))) {
            return ResultFactory.notApplicable();
        }

        Set<Rule> deletedRRules, remainingRRules, deletedSRules, remainingSRules;
        deletedRRules = new LinkedHashSet<Rule>();
        remainingRRules = new LinkedHashSet<Rule>();
        deletedSRules = new LinkedHashSet<Rule>();
        remainingSRules = new LinkedHashSet<Rule>();
        if (Globals.useAssertions) {
            assert(!R.isEmpty());
        }
        aborter.checkAbortion();

        ExportableOrder<TRSTerm> order = solver.solveRRR(RandS, aborter);
        if (order == null) {
            return ResultFactory.unsuccessful();
        }

        // Split rules in removed and not-removed rules

        for (Rule rule : R) {
            aborter.checkAbortion();
            if (order.inRelation(rule.getLeft(), rule.getRight())) {
                deletedRRules.add(rule);
            } else {
                Constraint<TRSTerm> cons = Constraint.create(rule.getLeft(), rule.getRight(), OrderRelation.GE);
                if (Globals.useAssertions) {
                    assert(order.solves(cons)) : "Constraint not solved: " + cons;
                }
                if (!order.solves(cons)) {
                    return ResultFactory.unsuccessful();
                }
                remainingRRules.add(rule);
            }
        }

        for (Rule rule : S) {
            aborter.checkAbortion();
            if (order.inRelation(rule.getLeft(), rule.getRight())) {
                deletedSRules.add(rule);
            } else {
                Constraint<TRSTerm> cons = Constraint.create(rule.getLeft(), rule.getRight(), OrderRelation.GE);
                if (Globals.useAssertions) {
                    assert(order.solves(cons)) : "Constraint not solved: " + cons;
                }
                if (!order.solves(cons)) {
                    return ResultFactory.unsuccessful();
                }
                remainingSRules.add(rule);
            }
        }

        if (Globals.useAssertions) {
            assert(!(deletedRRules.isEmpty() && deletedSRules.isEmpty())) : "No rules were deleted.";
        }

        if (deletedRRules.isEmpty() && deletedSRules.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        ImmutableSet<Rule> newSubProblemRRules, newSubProblemSRules;
        newSubProblemRRules = ImmutableCreator.create(remainingRRules);
        newSubProblemSRules = ImmutableCreator.create(remainingSRules);
        RelTRSProblem newSubProblem;
        newSubProblem = problem.createSubProblem(newSubProblemRRules, newSubProblemSRules);
        RelTRSProof proof = new RelTRSRRRProof(problem, remainingRRules,
                remainingSRules, deletedRRules, deletedSRules, order,
                newSubProblem);

        Result result = ResultFactory.proved(newSubProblem, YNMImplication.EQUIVALENT, proof);
        return result;
    }


    public static class RelTRSRRRProof extends RelTRSProof {

        private final RelTRSProblem problem;
        private final Set<Rule> remainingRRules, remainingSRules,
                deletedRRules, deletedSRules;
        private final ExportableOrder<TRSTerm> order;
        private final RelTRSProblem resultObl;

        public RelTRSRRRProof(final RelTRSProblem problem,
                final Set<Rule> remainingRRules,
                final Set<Rule> remainingSRules, final Set<Rule> deletedRRules,
                final Set<Rule> deletedSRules,
                final ExportableOrder<TRSTerm> order,
                final RelTRSProblem resultObl) {

            this.problem = problem;
            this.remainingRRules = remainingRRules;
            this.remainingSRules = remainingSRules;
            this.deletedRRules = deletedRRules;
            this.deletedSRules = deletedSRules;
            this.order = order;
            this.resultObl = resultObl;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {

            StringBuilder result;
            result = new StringBuilder();
            result.append("We used the following monotonic ordering for rule removal:");
            result.append(o.linebreak());
            result.append(o.export(this.order));
            result.append("With this ordering the following rules can be removed "+o.cite(Citation.MATRO)+ " because they are oriented strictly:");
            result.append(o.linebreak());
            result.append("Rules from R:");
            result.append(o.linebreak());
            result.append(o.set(this.deletedRRules, Export_Util.RULES));
            result.append("Rules from S:");
            result.append(o.linebreak());
            result.append(o.set(this.deletedSRules, Export_Util.RULES));
            result.append(o.newline());
            result.append(o.cond_linebreak());
            return result.toString();
        }


        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            if (modus.isPositive()) {
                return CPFTag.RELATIVE_TERMINATION_PROOF.create(doc,
                        CPFTag.RULE_REMOVAL.create(doc,
                        this.order.toCPF(doc, xmlMetaData),
                        CPFTag.trs(doc, xmlMetaData, this.remainingRRules),
                        CPFTag.trs(doc, xmlMetaData, this.remainingSRules),
                        childrenProofs[0]));
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultObl);
            }
        }

        @Override
        public String getNonCPFExportableReason(CPFModus modus) {
            return super.getNonCPFExportableReason(modus) + " with " + this.order.isCPFSupported();
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return (!modus.isPositive() || this.order.isCPFSupported() == null);
        }

    }
}
