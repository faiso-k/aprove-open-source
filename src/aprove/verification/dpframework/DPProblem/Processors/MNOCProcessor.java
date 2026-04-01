package aprove.verification.dpframework.DPProblem.Processors;

import java.util.logging.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;


/**
 * Processor which checks if it suffices to handle (P,lhs(R),R,m) instead of (P,Q,R,m).
 * (see thesis Theorem 3.14)
 *
 * This transformation is sound and complete if the following
 * four condition hold:
 *
 * (1) for all s -> t in P non-variable subterms of s do not unify with
 *     left-hand sides of rules from R (after variable renaming)
 * (2) the relation -Q->_R is locally confluent (on the set of terminating terms)
 * (3) NF(R) is a subset of NF(Q)
 * (4) f = m
 *
 * Since it is undecidable if an arbitrary trs is locally confluent the processor
 * tries to join all critical pairs in finitely many steps. The number of steps
 * is given by the attribute 'testDepth'.
 * If Q is non-empty then local confluence will be guaranteed by only trivial critical
 * pairs (see thesis Lemma 3.19)
 *
 * In REVERSED MODE the processor tries to replace (P,Q,R,f) by (P,empty,R,a)
 * (see thesis Theorem 8.9)
 * This is useful for disproving termination.
 *
 * Conditions:
 *
 * (1) for all s -> t in P non-variable subterms of s do not unify with
 *     left-hand sides of rules from R (after variable renaming)
 * (2) the relation ->_R is locally confluent
 * (3) NF(R) is a subset of NF(Q)
 * (4) Q-termination of R implies termination of R
 *
 * Condition (4) is currently ensured by checking that R is overlay
 * (then by (2) innermost termination implies termination,
 *  and using (3) Q-termination implies innermost termination)
 *
 *
 *
 * @author Matthias Sondermann, Rene Thiemann
 * @version $Id$
 */
public class MNOCProcessor extends QDPProblemProcessor {

    private final static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.MNOCProcessor");

    /**
     * number of steps to join critical pairs
     */
    private final int testDepth;

    /**
     * from termination to innermost termination or reversed?
     */
    private final boolean reversed;

    @ParamsViaArgumentObject
    public MNOCProcessor(final Arguments arguments) {
        this.testDepth = arguments.testDepth;
        this.reversed = arguments.reversed;
    }

    @Override
    public Result processQDPProblem(final QDPProblem qdpProblem, final Abortion abortion) throws AbortionException {
        final ImmutableSet<Rule> P = qdpProblem.getP();
        final QTRSProblem QR = qdpProblem.getRwithQ();
        final ImmutableSet<Rule> R = QR.getR();

        // check R does not reach into P
        if (!MNOCProcessor.rDoesNotOverlapWithP(R, P, QR.getRuleMap())) {
            return ResultFactory.unsuccessful();
        }

        abortion.checkAbortion();

        if (this.reversed) {
            final CriticalPairs critPairs = QR.getCriticalPairs();



            // check R is overlay (used to later on ensure that
            // termination of R implies Q-termination of R by local confluence)
            if (!critPairs.isOverlay(abortion)) {
                return ResultFactory.unsuccessful();
            }

            // check ->_R is loc. confluent
            if (critPairs.isLocallyConfluent(this.testDepth, abortion) != YNM.YES) {
                return ResultFactory.unsuccessful();
            }

            final QDPProblem newQdpProblem = qdpProblem.getTerminationProblem();
            return ResultFactory.proved(newQdpProblem, YNMImplication.EQUIVALENT, new MNOCProof(qdpProblem,
                newQdpProblem, true, this.testDepth));




        } else {
            // check local confluence of -Q->_R
            if (QR.getQ().isEmpty()) {
                // for ->_R use standard criterion
                if (QR.getCriticalPairs().isLocallyConfluent(this.testDepth, abortion) != YNM.YES) {
                    return ResultFactory.unsuccessful();
                }
            } else {
                // for non-empty Q test for trivial critical pairs
                if (!QR.getCriticalPairs().onlyTrivialCriticalPairs(abortion)) {
                    return ResultFactory.unsuccessful();
                }
            }

            final QDPProblem newQdpProblem = qdpProblem.getInnermostProblem();
            return ResultFactory.proved(newQdpProblem, YNMImplication.EQUIVALENT, new MNOCProof(qdpProblem,
                newQdpProblem, false, this.testDepth));
        }
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {

        final QTRSProblem QR = qdp.getRwithQ();
        final QTermSet Q = QR.getQ();
        final ImmutableSet<Rule> R = QR.getR();

        if (this.reversed) {

            // check whether we can gain something
            if (Q.isEmpty()) {
                MNOCProcessor.log.log(Level.CONFIG, "RMNOC processor is not applicable because we are already in termination case!\n");
                return false;
            }


            // check nf(R) subseteq nf(Q)
            final QTermSet lhsR = new QTermSet(CollectionUtils.getLeftHandSides(R));
            if (!lhsR.canAllBeRewritten(Q.getTerms())) {
                MNOCProcessor.log.log(Level.CONFIG, "RMNOC processor is not applicable because NF(R) is not a subset of NF(Q)!\n");
                return false;
            }

            return true;

        } else {
            // check whether we can gain something
            if (QR.QsupersetOfLhsR()) {
                MNOCProcessor.log.log(Level.CONFIG, "MNOC processor is not applicable because we are already in innermost case!\n");
                return false;
            }

            // f = m ?
            if(!qdp.getMinimal()) {
                MNOCProcessor.log.log(Level.CONFIG, "MNOC processor is not applicable because f != m\n");
                return false;
            }

            // check nf(R) subseteq nf(Q)
            final QTermSet lhsR = new QTermSet(CollectionUtils.getLeftHandSides(R));
            if (!lhsR.canAllBeRewritten(Q.getTerms())) {
                MNOCProcessor.log.log(Level.CONFIG, "MNOC processor is not applicable because NF(R) is not a subset of NF(Q)!\n");
                return false;
            }

            return true;
        }
    }

    /**
     * Checks if for all s->t from P, non-variable subterms of s do not unify with lhs of rules from R (after variable renaming)
     */
    static boolean rDoesNotOverlapWithP(final ImmutableSet<Rule> R, final ImmutableSet<Rule> P, final ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> rMap) {
        ImmutableSet<Rule> usefulRules;
        for(final Rule pRule : P) {
            final TRSTerm pLhs = pRule.getLeft().renumberVariables(TRSTerm.SECOND_STANDARD_PREFIX);
            for(final TRSFunctionApplication pSub : pLhs.getNonVariableSubTerms()) {
                if((usefulRules = rMap.get(pSub.getRootSymbol())) == null) {
                    continue;
                }
                for(final Rule rRule : usefulRules) {
                    if(rRule.getLhsInStandardRepresentation().unifies(pSub)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }



    /**
     * Proof of MNOC Processor
     *
     * @author Matthias Sondermann
     */
    private static final class MNOCProof extends QDPProof {

        private final boolean reversed;
        private final QDPProblem origQDP;
        private final QDPProblem newQDP;
        private final int testDepth;


        private MNOCProof(final QDPProblem origQDP, final QDPProblem newQDP, final boolean reversed, final int testDepth) {
            this.reversed = reversed;
            this.origQDP = origQDP;
            this.newQDP = newQDP;
            this.testDepth = testDepth * 10;
            // since the testDepth in criticalPairs uses parallel rewriting,
            // the sequential number may be higher. Multiplying by 10 is just
            // some heuristic value.
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            if (this.reversed) {
                sb.append("We use the modular non-overlap check "+eu.cite(Citation.FROCOS05)+" to decrease Q to the empty set.");
            } else {
                sb.append("We use the modular non-overlap check "+eu.cite(Citation.LPAR04)+" to enlarge Q to all left-hand sides of R.");
            }

            return sb.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            final Element mnocProof;
            final Element wcrProof = CPFTag.WCR_PROOF.create(
                    doc,CPFTag.JOINABLE_CRITICAL_PAIRS_B_F_S.create(
                        doc,
                        doc.createTextNode(this.testDepth + "")));
            if (modus.isPositive()) {
                if (this.reversed) {
                    mnocProof =
                        CPFTag.DP_PROOF.create(doc, CPFTag.INNERMOST_LHSS_REMOVAL_PROC.create(
                            doc,
                            CPFTag.INNERMOST_LHSS.create(doc),
                            childrenProofs[0]));
                } else {
                    mnocProof =
                        CPFTag.DP_PROOF.create(
                            doc,
                            CPFTag.SWITCH_INNERMOST_PROC.create(doc, wcrProof, childrenProofs[0]));
                }
            } else {
                if (this.reversed) {
                    mnocProof =
                        CPFTag.DP_NONTERMINATION_PROOF.create(
                            doc,
                            CPFTag.SWITCH_FULL_STRATEGY_PROC.create(
                                doc,
                                wcrProof,
                                childrenProofs[0]));

                } else {
                    mnocProof =
                        CPFTag.DP_NONTERMINATION_PROOF.create(doc, CPFTag.INNERMOST_LHSS_INCREASE_PROC.create(
                            doc,
                            this.newQDP.getQ().toCPF(doc, xmlMetaData),
                            childrenProofs[0]));

                }
            }
            return mnocProof;
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }

    public static class Arguments {
        public boolean reversed = false;
        public int testDepth;
    }

}
