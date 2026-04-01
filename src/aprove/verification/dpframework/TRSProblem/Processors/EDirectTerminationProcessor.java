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
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import aprove.xml.*;

/**
 * checks whether all rules can be ordered strictly by a reduction order ac-compatible to equations of e
 *
 * @author stein
 * @version $Id$
 */
public class EDirectTerminationProcessor extends ETRSProcessor {

    private final SolverFactory factory;

    @ParamsViaArguments("Order")
    public EDirectTerminationProcessor(SolverFactory order) {
        this.factory = order;
    }

    @Override
    public boolean isETRSApplicable(ETRSProblem qtrs) {
        return this.factory.isACCompatible() && (!Options.certifier.isCpf() || this.factory.deliversCPForders());
    }

    @Override
    protected Result processETRS(ETRSProblem etrs, Abortion aborter) throws AbortionException {
        Set<Rule> R = etrs.getR();
        Set<Equation> E = etrs.getE();
        if (Globals.useAssertions) {
            assert(!R.isEmpty() &&
                    etrs.checkACandAandC());
        }

        aborter.checkAbortion();

        Set<Constraint<TRSTerm>> cs = Constraint.fromRules(R, OrderRelation.GR);
        cs.addAll(Constraint.fromEquations(E));
        AbortableConstraintSolver<TRSTerm> solver =
            this.factory.getACSolver(cs, etrs.getSignatureOfR(),
                    etrs.getASymbols(), etrs.getACSymbols(), etrs.getCSymbols());
        ExportableOrder<TRSTerm> order = solver.solve(cs, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful();
        }

        if (Globals.useAssertions) {
            for (Constraint<TRSTerm> c : cs) {
                assert order.solves(c);
            }
        }

        ETRSProof proof = new EDirectTerminationProof(order, R);

        return ResultFactory.proved(proof);
    }

    private static class EDirectTerminationProof extends ETRSProof {

        private final ExportableOrder<TRSTerm> order;
        private final Set<Rule> rules;

        private EDirectTerminationProof(ExportableOrder<TRSTerm> order, Set<Rule> rules) {
            if (Globals.useAssertions) {
                assert(order != null);
            }
            this.order = order;
            this.rules = rules;
        }


        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append(o.export("We use "+o.cite(Citation.DA_FALKE)+" with the following order to prove termination."+o.linebreak()));
            s.append(o.cond_linebreak());
            s.append(o.export(this.order));
            s.append(o.cond_linebreak());
            return s.toString();
        }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            return CPFTag.AC_TERMINATION_PROOF.create(doc,
                    CPFTag.AC_RULE_REMOVAL.create(doc,
                    this.order.toCPF(doc, xmlMetaData),
                    CPFTag.trs(doc, xmlMetaData, this.rules),
                        CPFTag.AC_TERMINATION_PROOF.create(doc, CPFTag.AC_R_IS_EMPTY.create(doc))));
        }

        @Override
        public String getNonCPFExportableReason(CPFModus modus) {
            return super.getNonCPFExportableReason(modus) + " with " + this.order.isCPFSupported();
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return this.order.isCPFSupported() == null && modus.isPositive();
        }

    }

}
