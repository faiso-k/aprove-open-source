/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * checks whether some proper subterm of l from a rule l -> r in R can be rewritten by Q.
 * If this is the case then we can delete l->r from R!
 *
 * Also checks whether some s from a rule s -> t in P can be rewritten by Q.
 * If this is the case then we can delete s->t from P!
 *
 * This processor deletes all rules of the above structure. Hence,
 * it does not make sense to call this processor more than once.
 *
 * @author thiemann
 */
@NoParams
public class RRR_Q_Processor extends QDPProblemProcessor {

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return qdp.isRRRQreducable();
    }


    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        final QTermSet Q = qdp.getQ();

        Set<Rule> deletedFromR;
        Set<Rule> keptFromR;

        final QTRSProblem qtrs = qdp.getRwithQ();
        if (qtrs.isRRRQreducable()) {
            deletedFromR = new LinkedHashSet<Rule>();
            keptFromR = new LinkedHashSet<Rule>();
            for (final Rule rule : qtrs.getR()) {
                boolean delete = false;
                for (final TRSTerm subTerm : rule.getLeft().getArguments()) {
                    delete = Q.canBeRewritten(subTerm);
                    if (delete) {
                        break;
                    }
                }
                if (delete) {
                    deletedFromR.add(rule);
                } else {
                    keptFromR.add(rule);
                }
            }

            // this can be assumed from isApplicable-Check
            assert(!deletedFromR.isEmpty());
        } else {
            deletedFromR = null;
            keptFromR = null;
        }


        Set<Rule> deletedFromP = new LinkedHashSet<Rule>();
        final Set<Rule> keptFromP = new LinkedHashSet<Rule>();
        for (final Rule dp : qdp.getP()) {
            if (Q.canBeRewritten(dp.getLeft())) {
                deletedFromP.add(dp);
            } else {
                keptFromP.add(dp);
            }
        }

        if (deletedFromP.isEmpty()) {
            deletedFromP = null;
        }

        // we have done something
        assert(deletedFromR != null || deletedFromP != null);
        QDPProblem newQdp;
        if (deletedFromR == null) {
            newQdp = qdp.getSubProblem(ImmutableCreator.create(keptFromP));
        } else {
            if (deletedFromP == null) {
                newQdp = qdp.getSubProblemWithSmallerR(ImmutableCreator.create(keptFromR));
            } else {
                newQdp = qdp;
            }
            newQdp = newQdp.getSubProblem(ImmutableCreator.create(keptFromP),
                    ImmutableCreator.create(keptFromR));
            newQdp.getRwithQ().setRRRQreducable(false);
        }

        newQdp.setRRRQreducable(false);

        final QDPProof proof = new RRR_Q_Proof(deletedFromP, deletedFromR, qdp, newQdp);

        return ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);
    }

    private static class RRR_Q_Proof extends QDPProof {

        private final QDPProblem origQdp, resultQdp;
        private final Set<Rule> deletedFromP;
        private final Set<Rule> deletedFromR;

        private RRR_Q_Proof(final Set<Rule> deletedFromP,
            final Set<Rule> deletedFromR,
            final QDPProblem origQdp,
            final QDPProblem resultQdp)
        {
            this.deletedFromP = deletedFromP;
            this.deletedFromR = deletedFromR;
            this.origQdp = origQdp;
            this.resultQdp = resultQdp;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuffer s = new StringBuffer();
            if (this.deletedFromP != null) {
                s.append(o.export("We deleted the following rules from P as their lhs contain Q-redexes and are hence obviously never member of a chain."));
                s.append(o.cond_linebreak());
                s.append(o.set(this.deletedFromP, Export_Util.RULES));
                s.append(o.cond_linebreak());
            }
            if (this.deletedFromR != null) {
                s.append(o.export("We deleted the following rules from R as their lhs contain Q-redexes on non-root position and can hence never be used."));
                s.append(o.cond_linebreak());
                s.append(o.set(this.deletedFromR, Export_Util.RULES));
                s.append(o.cond_linebreak());
            }
            s.append(o.cite(Citation.THIEMANN));
            return s.toString();
        }

        public String toBibTeX() {
            return "";
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            if (this.isCPFCheckableProof(modus)) {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultQdp);
            } else {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

    }


}
