/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * checks whether some proper subterm of l from a rule l -> r in R can be rewritten by Q.
 * If this is the case then we can delete l->r from R!
 *
 * This processor deletes all rules of the above structure. Hence,
 * it does not make sense to call this processor more than once.
 *
 * @author thiemann
 */
@NoParams
public class RRR_Q_Processor extends QTRSProcessor {

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return qtrs.isRRRQreducable();
    }


    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final QTermSet Q = qtrs.getQ();
        final Set<Rule> R = qtrs.getR();

        final Set<Rule> deleted = new LinkedHashSet<>();
        final Set<Rule> keep = new LinkedHashSet<>();
        for (final Rule rule : R) {
            aborter.checkAbortion();
            boolean delete = false;
            for (final TRSTerm subTerm : rule.getLeft().getArguments()) {
                delete = Q.canBeRewritten(subTerm);
                if (delete) {
                    break;
                }
            }
            if (delete) {
                deleted.add(rule);
            } else {
                keep.add(rule);
            }
        }

        assert(Collections.disjoint(keep, deleted));
        assert(keep.size() + deleted.size() == R.size());

        // this can be assumed from isApplicable-Check
        assert(!deleted.isEmpty());

        final ImmutableSet<Rule> rNew = ImmutableCreator.create(keep);
        final QTRSProblem newProblem = qtrs.createSubProblem(rNew);

        final QTRSProof proof = new RRR_Q_Proof(qtrs, newProblem, ImmutableCreator.create(deleted));

        newProblem.setRRRQreducable(false);

        return ResultFactory.proved(newProblem, YNMImplication.EQUIVALENT, proof);
    }

    static class RRR_Q_Proof extends QTRSProof {

        private final BasicObligation origProblem;
        private final QTRSProblem newProblem;
        private final ImmutableSet<? extends GeneralizedRule> deletedRules;

        RRR_Q_Proof(final BasicObligation origProblem, final QTRSProblem newProblem,
                final ImmutableSet<? extends GeneralizedRule> deleteRules) {
            assert(deleteRules != null);
            this.origProblem = origProblem;
            this.newProblem = newProblem;
            this.deletedRules = deleteRules;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuffer s = new StringBuffer();
            s.append(o.export("We deleted the following rules from R as their lhs contain Q-redexes on non-root position."));
            s.append(o.cond_linebreak());
            s.append(o.set(this.deletedRules, Export_Util.RULES));
            s.append(o.cond_linebreak());
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
            if (modus.isPositive()) {
                return CPFTag.TRS_TERMINATION_PROOF.create(doc,
                        CPFTag.REMOVE_NON_APPLICABLE_RULES.create(doc,
                                CPFTag.trs(doc, xmlMetaData, this.deletedRules),
                                childrenProofs[0]));
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.newProblem);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }


}
