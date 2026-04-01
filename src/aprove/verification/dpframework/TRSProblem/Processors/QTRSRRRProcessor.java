
package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
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
 * Remove Redundant Rules Processor for arbitrary orders.
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class QTRSRRRProcessor extends QTRSProcessor {

    private final SolverFactory factory;

    @ParamsViaArguments("Order")
    public QTRSRRRProcessor(final SolverFactory order) {
        this.factory = order;
    }

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return true;
    }

    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {

        final Set<Rule> R = qtrs.getR();
        final RRRSolver solver = this.factory.getRRRSolver();
        if (!solver.isRRRApplicable(R)) {
            return ResultFactory.notApplicable();
        }

        Set<Rule> deletedRules, remainingRules;
        deletedRules = new LinkedHashSet<Rule>();
        remainingRules = new LinkedHashSet<Rule>();
        if (Globals.useAssertions) {
            assert(!R.isEmpty());
        }
        aborter.checkAbortion();

        final ExportableOrder<TRSTerm> order = solver.solveRRR(R, aborter);
        if (order == null) {
            return ResultFactory.unsuccessful();
        }

        // Split rules in removed and not-removed rules

        for (final Rule rule : R) {
            aborter.checkAbortion();
            if (order.inRelation(rule.getLeft(), rule.getRight())) {
                deletedRules.add(rule);
            } else {
                final Constraint<TRSTerm> cons = Constraint.create(rule.getLeft(), rule.getRight(), OrderRelation.GE);
                if (Globals.useAssertions) {
                    assert(order.solves(cons));
                }
                if (!order.solves(cons)) {
                    return ResultFactory.unsuccessful();
                }
                remainingRules.add(rule);
            }
        }

        if (Globals.useAssertions) {
            assert(!deletedRules.isEmpty()) : "No rules were deleted.";
        }

        if (deletedRules.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        ImmutableSet<Rule> newSubProblemRules;
        newSubProblemRules = ImmutableCreator.create(remainingRules);
        QTRSProblem newQtrs;
        newQtrs = qtrs.createSubProblem(newSubProblemRules);

        final Proof proof = new QTRSRRRProof(deletedRules, remainingRules, order, qtrs, newQtrs);
        final Result result = ResultFactory.proved(newQtrs, YNMImplication.EQUIVALENT, proof);
        return result;
    }

}

class QTRSRRRProof extends QTRSProof {

        private final Set<Rule> deletedRules;
        private final Set<Rule> remainingRules;
        private final ExportableOrder<TRSTerm> order;
        private final QTRSProblem origObl;
        private final QTRSProblem resultObl;

    QTRSRRRProof(
        final Set<Rule> deletedRules,
        final Set<Rule> remainingRules,
        final ExportableOrder<TRSTerm> order,
        final QTRSProblem origObl,
        final QTRSProblem resultObl)
    {
            if (Globals.useAssertions) {
                assert(order != null);
            }
            this.deletedRules = deletedRules;
            this.remainingRules = remainingRules;
            this.order = order;
            this.origObl = origObl;
            this.resultObl = resultObl;
        }

        @Override
        public String export(final Export_Util o, VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append("Used ordering:");
            result.append(o.linebreak());
            result.append(o.export(this.order));
            result.append("With this ordering the following rules can be removed by the rule removal processor "+o.cite(Citation.LPAR04)+ " because they are oriented strictly:");
            result.append(o.linebreak());
            result.append(o.set(this.deletedRules, Export_Util.RULES));
            result.append(o.newline());
            result.append(o.linebreak());
            return result.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            if (modus.isPositive()) {
                return CPFTag.TRS_TERMINATION_PROOF.create(doc,
                        CPFTag.RULE_REMOVAL.create(doc,
                        this.order.toCPF(doc, xmlMetaData),
                        CPFTag.trs(doc, xmlMetaData, this.remainingRules),
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

