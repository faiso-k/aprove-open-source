package aprove.verification.dpframework.CSDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

@NoParams
public class QCSDPNarrowingProcessor
        extends QCSDPTransformationProcessor {

    @Override
    protected TransformationInfo applyTransformation(QCSDPProblem problem,
            Rule s_to_t, GeneralizedTRS r) {
        if (Globals.useAssertions) {
            assert (s_to_t.checkVariablePrefix(TRSTerm.SECOND_STANDARD_PREFIX));
        }

        ReplacementMap rm = problem.getReplacementMap();
        QTermSet q = problem.getQ();

        // check if NF_mu(Q) \subseteq NF_mu(R) (innermost)
        boolean innermost = problem.isInnermost();

        /* TODO for now only allow full termination or innermost termination */
        if (!innermost && !q.isEmpty()) {
            return null;
        }

        TRSFunctionApplication s = s_to_t.getLeft();
        TRSTerm t = s_to_t.getRight();

        /* for full termination, restrict to linear rhs */
        if (!innermost && !t.isLinear()) {
            return null;
        }

        /* conservativeness is required for both, innermost and full */
        if (!rm.isConservative(s_to_t)) {
            return null;
        }

        /*
         * check that at least one R step is required to continue after the pair
         * s -> t
         */
        for (Rule pair : problem.getDp()) {
            TRSSubstitution delta = t
                    .getMGU(pair.getLhsInStandardRepresentation());

            if (delta == null) {
                continue;
            }

            if (!innermost) {
                return null;
            }

            TRSFunctionApplication v = pair.getLeft();

            /*
             * in the innermost case, if an mgu delta exists either s\delta or
             * v\delta must be in no Q-mu-normal form
             */
            if (rm.inQMuNormalForm(q, v.applySubstitution(delta))
                    && rm.inQMuNormalForm(q, s.applySubstitution(delta))) {
                return null;
            }
        }

        /* finally all preconditions are met, now do the narrowing step */
        Set<Rule> newPairs = new LinkedHashSet<Rule>();

        if (!t.isVariable()) {
            Set<Pair<TRSTerm, TRSSubstitution>> tNarrowed = this.computeNarrowings(
                    (TRSFunctionApplication) t, rm, problem.getRWithQ());
            for (Pair<TRSTerm, TRSSubstitution> ts : tNarrowed) {
                TRSSubstitution sigma = ts.getValue();

                TRSFunctionApplication lhs = s_to_t.getLeft().applySubstitution(
                        sigma);

                /* check normal-form in innermost case */
                if (innermost && !rm.inQMuNormalForm(q, lhs)) {
                    continue;
                }

                TRSTerm rhs = ts.getKey();
                Rule newPair = Rule.create(lhs, rhs);
                newPairs.add(newPair);
            }
        }

        return new TransformationInfo(false, false, ImmutableCreator
                .create(newPairs));
    }

    private Set<Pair<TRSTerm, TRSSubstitution>> computeNarrowings(
            TRSFunctionApplication t, ReplacementMap rm, QTRSProblem rWithQ) {
        Set<Pair<TRSTerm, TRSSubstitution>> tNarrowed = new LinkedHashSet<Pair<TRSTerm, TRSSubstitution>>();

        FunctionSymbol f = t.getRootSymbol();
        int n = f.getArity();
        Set<Integer> map = rm.getMap().get(f);

        /* compute narrowings of every \mu-replacing argument position */
        for (int i : map) {
            TRSTerm t_i = t.getArgument(i);

            /* skip variables in narrowing step */
            if (t_i.isVariable()) {
                continue;
            }

            Set<Pair<TRSTerm, TRSSubstitution>> t_iNarrowed = this.computeNarrowings(
                    (TRSFunctionApplication) t_i, rm, rWithQ);

            /* build new t narrowing for every t_i narrowing */
            for (Pair<TRSTerm, TRSSubstitution> ts : t_iNarrowed) {
                TRSSubstitution sigma = ts.getValue();
                TRSTerm t_iN = ts.getKey();

                ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(n);
                for (int j = 0; j < n; ++j) {
                    if (i == j) {
                        args.add(t_iN);
                    } else {
                        args.add(t.getArgument(j).applySubstitution(sigma));
                    }
                }

                TRSFunctionApplication tN = TRSTerm
                        .createFunctionApplication(f, ImmutableCreator
                                .create(args));

                tNarrowed.add(new Pair<TRSTerm, TRSSubstitution>(tN, sigma));
            }
        }

        /* finally try to apply a rule to the root position of t */
        if (rWithQ.getRuleMap().containsKey(f)) {
            for (Rule l_to_r : rWithQ.getRuleMap().get(f)) {
                TRSFunctionApplication lhs = l_to_r
                        .getLhsInStandardRepresentation();
                TRSTerm rhs = l_to_r.getRhsInStandardRepresentation();

                TRSSubstitution mgu = t.getMGU(lhs);
                if (mgu == null) {
                    continue;
                }

                tNarrowed.add(new Pair<TRSTerm, TRSSubstitution>(rhs
                        .applySubstitution(mgu), mgu));
            }
        }

        return tNarrowed;
    }

    @Override
    protected String getTransformationName() {
        return "Context-Sensitive Narrowing";
    }

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem obl) {
        return true;
    }

    @Override
    protected Citation[] getCitations() {
        return new Citation[] { Citation.DA_EMMES };
    }

}
