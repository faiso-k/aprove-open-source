package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;


/**
 * Taken from QDP.
 *
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
 * @author mpluecke
 * @version $Id$
 */
public class IDPMNOCProcessor extends IDPProcessor {

    private static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.MNOCProcessor");

    /**
     * number of steps to join critical pairs
     */
    private final int testDepth;

    /**
     * from termination to innermost termination or reversed?
     */
    private final boolean reversed;

    @ParamsViaArgumentObject
    public IDPMNOCProcessor(Arguments arguments) {
        this.reversed = arguments.reversed;
        this.testDepth = arguments.testDepth;
    }

    @Override
    public Result processIDPProblem(IDPProblem idpProblem, Abortion abortion) throws AbortionException {
        ImmutableSet<? extends GeneralizedRule> P = idpProblem.getP();
        ImmutableSet<? extends GeneralizedRule> R = idpProblem.getR();

        // check R does not reach into P
        if (!IDPMNOCProcessor.rDoesNotOverlapWithP(R, P, idpProblem.getRuleAnalysis().getRAnalysis().getRuleMap())) {
            return ResultFactory.unsuccessful();
        }

        abortion.checkAbortion();

        if (this.reversed) {
            CriticalPairs critPairs = idpProblem.getRuleAnalysis().getRAnalysis().getCriticalPairs();



            // check R is overlay (used to later on ensure that
            // termination of R implies Q-termination of R by local confluence)
            if (!critPairs.isOverlay(abortion)) {
                return ResultFactory.unsuccessful();
            }

            // check ->_R is loc. confluent
            if (critPairs.isLocallyConfluent(this.testDepth, abortion) != YNM.YES) {
                return ResultFactory.unsuccessful();
            }

            IDPProblem newidpProblem = idpProblem.change(null, null, new IQTermSet(new QTermSet(java.util.Collections.<TRSFunctionApplication>emptySet()), idpProblem.getRuleAnalysis().getPreDefinedMap()), null, this);
            return ResultFactory.proved(newidpProblem, YNMImplication.EQUIVALENT, new MNOCProof(true));

        } else {
            // check local confluence of -Q->_R
            if (idpProblem.getRuleAnalysis().getQ().isEmpty()) {
                // for ->_R use standard criterion
                if (idpProblem.getRuleAnalysis().getRAnalysis().getCriticalPairs().isLocallyConfluent(this.testDepth, abortion) != YNM.YES) {
                    return ResultFactory.unsuccessful();
                }
            } else {
                // for non-empty Q test for trivial critical pairs
                if (!idpProblem.getRuleAnalysis().getRAnalysis().getCriticalPairs().onlyTrivialCriticalPairs(abortion)) {
                    return ResultFactory.unsuccessful();
                }
            }

            IDPProblem newidpProblem = idpProblem.change(null, null, new IQTermSet(new QTermSet(idpProblem.getRuleAnalysis().getRAnalysis().getLeftHandSides()), idpProblem.getRuleAnalysis().getPreDefinedMap()), null, this);
            return ResultFactory.proved(newidpProblem, YNMImplication.EQUIVALENT, new MNOCProof(false));
        }
    }

    @Override
    public boolean isIDPApplicable(IDPProblem idp) {

        IQTermSet Q = idp.getRuleAnalysis().getQ();

        if (this.reversed) {

            // check whether we can gain something
            if (Q.isEmpty()) {
                IDPMNOCProcessor.log.log(Level.CONFIG, "RMNOC processor is not applicable because we are already in termination case!\n");
                return false;
            }


            // check nf(R) subseteq nf(Q)
            IQTermSet lhsR = new IQTermSet(new QTermSet(idp.getRuleAnalysis().getRAnalysis().getLeftHandSides()), idp.getRuleAnalysis().getPreDefinedMap());
            // FIXME: proof that Q.getWrappedQ().getTerms()is ok!
            if (!lhsR.canAllBeRewritten(Q.getWrappedQ().getTerms())) {
                IDPMNOCProcessor.log.log(Level.CONFIG, "RMNOC processor is not applicable because NF(R) is not a subset of NF(Q)!\n");
                return false;
            }

            return true;

        } else {
            // check whether we can gain something
            if (idp.getRuleAnalysis().isNfQSubsetEqNfR()) {
                IDPMNOCProcessor.log.log(Level.CONFIG, "MNOC processor is not applicable because we are already in innermost case!\n");
                return false;
            }

            // f = m ?
            if(!idp.isMinimal()) {
                IDPMNOCProcessor.log.log(Level.CONFIG, "MNOC processor is not applicable because f != m\n");
                return false;
            }

            // check nf(R) subseteq nf(Q)
            IQTermSet lhsR = new IQTermSet(new QTermSet(idp.getRuleAnalysis().getRAnalysis().getLeftHandSides()), idp.getRuleAnalysis().getPreDefinedMap());
            // FIXME: proof that Q.getWrappedQ().getTerms()is ok!
            if (!lhsR.canAllBeRewritten(Q.getWrappedQ().getTerms())) {
                IDPMNOCProcessor.log.log(Level.CONFIG, "MNOC processor is not applicable because NF(R) is not a subset of NF(Q)!\n");
                return false;
            }

            return true;
        }
    }

    /**
     * Checks if for all s->t from P, non-variable subterms of s do not unify with lhs of rules from R (after variable renaming)
     */
    static boolean rDoesNotOverlapWithP(ImmutableSet<? extends GeneralizedRule> R, ImmutableSet<? extends GeneralizedRule> P, ImmutableMap<FunctionSymbol, ImmutableSet<GeneralizedRule>> rMap) {
        ImmutableSet<? extends GeneralizedRule> usefulRules;
        for(GeneralizedRule pRule : P) {
            TRSTerm pLhs = pRule.getLeft().renumberVariables(TRSTerm.SECOND_STANDARD_PREFIX);
            for(TRSFunctionApplication pSub : pLhs.getNonVariableSubTerms()) {
                if((usefulRules = rMap.get(pSub.getRootSymbol())) == null) {
                    continue;
                }
                for(GeneralizedRule rRule : usefulRules) {
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
    private static final class MNOCProof extends Proof.DefaultProof {

        private final boolean reversed;

        private MNOCProof(boolean reversed) {
            this.reversed = reversed;
        }

        @Override
        public String export(Export_Util eu, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            if (this.reversed) {
                sb.append("We use the modular non-overlap check "+eu.cite(Citation.FROCOS05)+" to decrease Q to the empty set.");
            } else {
                sb.append("We use the modular non-overlap check "+eu.cite(Citation.LPAR04)+" to enlarge Q to all left-hand sides of R.");
            }

            return sb.toString();
        }

    }

    public static class Arguments {
        public boolean reversed = false;
        public int testDepth;
    }

}
