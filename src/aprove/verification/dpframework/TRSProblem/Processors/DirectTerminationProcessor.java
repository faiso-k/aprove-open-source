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
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * checks whether all rules can be ordered strictly by a reduction order
 *
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class DirectTerminationProcessor extends QTRSProcessor {

    private final SolverFactory factory;

    @ParamsViaArguments("Order")
    public DirectTerminationProcessor(SolverFactory order) {
        this.factory = order;
    }


    @Override
    public boolean isQTRSApplicable(QTRSProblem qtrs) {
        return true;
    }

    @Override
    protected Result processQTRS(QTRSProblem qtrs, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        Set<Rule> R = qtrs.getR();
        if (Globals.useAssertions) {
            assert(!R.isEmpty());
        }

        aborter.checkAbortion();

        DirectSolver solver = this.factory.getDirectSolver();
        ExportableOrder<TRSTerm> order = solver.solveDirect(R, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful();
        }

        if (Globals.useAssertions) {
            Set<Constraint<TRSTerm>> cs = Constraint.fromRules(R, OrderRelation.GR);
            for (Constraint<TRSTerm> c : cs) {
                //System.out.println ("DEBUG: c="+c);
                assert order.inRelation(c.x, c.y);
            }
        }

        QTRSProof proof = new DirectTerminationProof(order);

        return ResultFactory.proved(proof);
    }

    private static class DirectTerminationProof extends QTRSProof {

        private final ExportableOrder<TRSTerm> order;

        private DirectTerminationProof(ExportableOrder<TRSTerm> order) {
            if (Globals.useAssertions) {
                assert(order != null);
            }
            this.order = order;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append(o.export("We use "+o.cite(Citation.DIRECT_TERMINATION)+" with the following order to prove termination."+o.linebreak()));
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
            return CPFTag.TRS_TERMINATION_PROOF.create(doc,
                    CPFTag.RULE_REMOVAL.create(doc,
                    this.order.toCPF(doc, xmlMetaData),
                    CPFTag.trs(doc, xmlMetaData, new HashSet<Rule>()),
                        CPFTag.TRS_TERMINATION_PROOF.create(doc, CPFTag.R_IS_EMPTY.create(doc))));
        }

        @Override
        public String getNonCPFExportableReason(CPFModus modus) {
            return super.getNonCPFExportableReason(modus) + " with " + this.order.isCPFSupported();
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return this.order.isCPFSupported() == null;
        }

    }
}
