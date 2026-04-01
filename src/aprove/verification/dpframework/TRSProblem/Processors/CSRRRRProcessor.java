package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Remove redundant rules processor for CSR problems with respect to mu monotonicity.
 * Given a CSR and a type of monotone ordering, tries to orient every rule non-strict
 * and at least one rule strict. Then removes all rules that are oriented strict.
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class CSRRRRProcessor extends CSRProcessor {

    private final SolverFactory factory;

    @ParamsViaArguments("Order")
    public CSRRRRProcessor(final SolverFactory order) {
        this.factory = order;
    }

    @Override
    public boolean isCSRApplicable(final CSRProblem csr) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        return true;
    }

    @Override
    protected Result processCSR(final CSRProblem csr, final Abortion aborter)
            throws AbortionException {
        final Set<Rule> R = csr.getR();
        final RRRMuSolver solver = this.factory.getRRRMuSolver();
        final ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu = csr.getReplacementMap();

        if (!solver.isRRRMuApplicable(R, mu)) {
            return ResultFactory.notApplicable();
        }

        Set<Rule> deletedRules, remainingRules;
        deletedRules = new LinkedHashSet<Rule>();
        remainingRules = new LinkedHashSet<Rule>();
        if (Globals.useAssertions) {
            assert(!R.isEmpty());
        }
        aborter.checkAbortion();

        final ExportableOrder<TRSTerm> order = solver.solveRRRMu(R, mu, aborter);
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
                if (Globals.DEBUG_THETUX) {
                    if (!order.solves(cons)) {
                        System.err.println("Constraint not solved!");
                        System.err.println("Order is:\n" + order + "\n");
                        System.err.println("Constraint is:\n" + cons + "\n");
                    }
                }
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
        CSRProblem newCsr;
        newCsr = csr.createSubProblem(newSubProblemRules);
        final CSRProof proof = new CSRRRRProof(csr, deletedRules, order, newCsr);

        final Result result = ResultFactory.proved(newCsr, YNMImplication.EQUIVALENT, proof);
        return result;
    }

    private static class CSRRRRProof extends CSRProof {

        private final CSRProblem csr;
        private final Set<Rule> deletedRules;
        private final ExportableOrder<TRSTerm> order;
        private final CSRProblem resultObl;

        private CSRRRRProof(
            final CSRProblem csr,
            final Set<Rule> deletedRules,
            final ExportableOrder<TRSTerm> order,
            final CSRProblem resultObl)
        {
            if (Globals.useAssertions) {
                assert(order != null);
            }
            this.csr = csr;
            this.deletedRules = deletedRules;
            this.order = order;
            this.resultObl = resultObl;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append("The following CSR is given: ");
            result.append(this.csr.export(o));
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
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultObl);
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

    }





}
