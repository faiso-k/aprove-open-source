package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Rule Removal processor. Using an arbitrary strongly monotonic
 * reduction pair, tries to orient all rules of P and R non-strictly
 * and at least one rule of P or R strictly, then deletes the strictly
 * oriented rules. (See Theorem 30 of LPAR04.)
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class MRRProcessor extends QDPProblemProcessor {

    private final SolverFactory factory;
    private final boolean allstrict;

    @ParamsViaArguments({"Order", "Allstrict"})
    public MRRProcessor(final SolverFactory factory, final boolean allstrict) {
        this.factory = factory;
        this.allstrict = allstrict;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.DPProblem.Processors.QDPProblemProcessor#processQDPProblem(aprove.verification.dpframework.DPProblem.QDPProblem, aprove.strategies.Abortions.Abortion)
     */
    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter)
            throws AbortionException {

        final Set<Rule> RP = new LinkedHashSet<Rule>(qdp.getR());
        RP.addAll(qdp.getP());

        ExportableOrder<TRSTerm> solvingOrder;
        if (this.allstrict) {
            final DirectSolver solver = this.factory.getDirectSolver();
            solvingOrder = solver.solveDirect(RP, aborter);
        } else {
            final RRRSolver solver = this.factory.getRRRSolver();
            solvingOrder = solver.solveRRR(RP, aborter);
        }
        return this.processQDPProblem(solvingOrder, qdp, aborter);
    }

    /**
     * Checks whether some rules in R or P of qdp are oriented strictly
     * by solvingOrder, removes them and generates an according proof.
     *
     * Requires that solvingOrder orients all rules of P and R in qdp at least
     * non-strictly.
     *
     * @param solvingOrder the order which is supposed to orient all rules in
     *  P united with R non-strictly
     * @param qdp the QDPProblem to simplify
     * @param aborter
     * @return the corresponding result
     */
    protected Result processQDPProblem(final ExportableOrder<TRSTerm> solvingOrder, final QDPProblem qdp,
                final Abortion aborter) throws AbortionException {
        if (solvingOrder == null) {
            return ResultFactory.unsuccessful();
        }

        ImmutableSet<Rule> p, r;
        p = qdp.getP();
        r = qdp.getR();

        // check which elements of P or R have been oriented strictly
        Set<Rule> newPRules, deletedPRules, newRRules, deletedRRules;
        newPRules = new LinkedHashSet<Rule>();
        deletedPRules = new LinkedHashSet<Rule>();
        newRRules = new LinkedHashSet<Rule>();
        deletedRRules = new LinkedHashSet<Rule>();
        for (final Rule rule : p) {
            aborter.checkAbortion();
            // only add non-strictly oriented rules
            if (! solvingOrder.inRelation(rule.getLeft(), rule.getRight())) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> constraint;
                    constraint = Constraint.create(rule.getLeft(),
                            rule.getRight(), OrderRelation.GE);
                    assert (solvingOrder.solves(constraint));
                }
                newPRules.add(rule);
            }
            else {
                deletedPRules.add(rule);
            }

        }
        for (final Rule rule : r) {
            // only add non-strictly oriented rules
            if (! solvingOrder.inRelation(rule.getLeft(), rule.getRight())) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> constraint;
                    constraint = Constraint.create(rule.getLeft(),
                            rule.getRight(), OrderRelation.GE);
                    assert (solvingOrder.solves(constraint));
                }
                newRRules.add(rule);
            }
            else {
                deletedRRules.add(rule);
            }

        }

        if (Globals.useAssertions) {
            assert (! (deletedPRules.isEmpty()
                    && deletedRRules.isEmpty()));
            if (this.allstrict) {
                assert newRRules.isEmpty();
                assert newPRules.isEmpty();
            }
        }

        // build smaller subproblem and the proof
        // different cases to be able to reuse some computed results of the current qdp problem
        QDPProblem newQdp;
        if (deletedRRules.isEmpty()) {
            newQdp = qdp.getSubProblem(ImmutableCreator.create(newPRules));
        } else if (deletedPRules.isEmpty()) {
            newQdp = qdp.getSubProblemWithSmallerR(ImmutableCreator.create(newRRules));
        } else {
            newQdp = qdp.getSubProblem(ImmutableCreator.create(newPRules), ImmutableCreator.create(newRRules));
        }
        final Proof proof = new MRRProof(deletedRRules, deletedPRules, solvingOrder, qdp, newQdp);
        final Result result = ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);

        return result;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return true;
    }

}


final class MRRProof extends QDPProof {

        private final Set<Rule> orientedRRules;
        private final Set<Rule> orientedPRules;
        private final ExportableOrder<TRSTerm> order;
        private final QDPProblem origQDP;
        private final QDPProblem resultQDP;


    MRRProof(
        final Set<Rule> orientedRRules,
        final Set<Rule> orientedPRules,
                final ExportableOrder<TRSTerm> order, final QDPProblem origQDP, final QDPProblem resultQDP) {
            if (Globals.useAssertions) {
                assert(! (orientedPRules.isEmpty()
                        && orientedRRules.isEmpty()));
            }
            this.orientedRRules = orientedRRules;
            this.orientedPRules = orientedPRules;
            this.order = order;
            this.origQDP = origQDP;
            this.resultQDP = resultQDP;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (true) { // TODO deal with level
                result.append("By using the rule removal processor "+o.cite(Citation.LPAR04)+" with the following ordering, at least one Dependency Pair or term rewrite system rule of this QDP problem can be strictly oriented.\n");
                result.append(o.cond_linebreak());
                if (! this.orientedPRules.isEmpty()) {
                    result.append("Strictly oriented dependency pairs:\n");
                    result.append(o.set(this.orientedPRules, Export_Util.RULES));
                }
                result.append(o.cond_linebreak());
                if (! this.orientedRRules.isEmpty()) {
                    result.append("Strictly oriented rules of the TRS R:\n");
                    result.append(o.set(this.orientedRRules, Export_Util.RULES));
                }
                result.append(o.cond_linebreak());
                result.append("Used ordering: ");
                result.append(o.export(this.order));
                result.append(o.cond_linebreak());
            }
            return result.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            if (modus.isPositive()) {
                return CPFTag.DP_PROOF.create(doc,
                        CPFTag.MONO_RED_PAIR_PROC.create(doc,
                                this.order.toCPF(doc, xmlMetaData),
                                CPFTag.dps(doc, xmlMetaData, this.resultQDP.getP()),
                                CPFTag.trs(doc, xmlMetaData, this.resultQDP.getR()),
                                childrenProofs[0]
                                ));
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultQDP);
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

