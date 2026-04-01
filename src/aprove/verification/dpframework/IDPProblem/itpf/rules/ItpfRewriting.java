package aprove.verification.dpframework.IDPProblem.itpf.rules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Logic.*;
import immutables.*;

/**
 *
 * @author mpluecke
 */
public class ItpfRewriting extends IItpfRule.ItpfRuleSkeleton {

    private static final Integer MAX_VALUE = Integer.valueOf(Integer.MAX_VALUE);
    private static final Integer ONE = Integer.valueOf(1);

    private final ExportableString longDescription;
    private final ExportableString shortDescription;
    private final int maxRewriteSteps;

    @ParamsViaArgumentObject
    public ItpfRewriting(final Arguments arguments) {
        this(arguments.maxRewriteSteps);
    }

    public static class Arguments {
        public int maxRewriteSteps = 10;
    }

    public ItpfRewriting(final int maxRewriteSteps) {
        this.maxRewriteSteps = maxRewriteSteps;
        this.shortDescription = this.longDescription = new ExportableString("ItpfRewriting");
    }

    @Override
    public Exportable getDescription(final NameLength length) {
        switch (length) {
        case SHORT :
            return this.shortDescription;
        case LONG :
            return this.longDescription;
        }
        return null;
    }


    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return idp.getRuleAnalysis().isNfQSubsetEqNfR();
    }

    @Override
    public boolean isApplicable(final IDPProblem idp, final Itpf formula, final ApplicationMode mode) {
        return idp.getRuleAnalysis().isNfQSubsetEqNfR();
    }


    @Override
    public Itpf process(final IDPProblem idp, final Itpf formula, final ApplicationMode mode,
            final Abortion aborter) throws AbortionException {
        final RewritingVisitor visitor = new RewritingVisitor(idp.getRuleAnalysis(), mode, this.maxRewriteSteps , aborter);
        return visitor.applyTo(formula.normalize());
    }

    protected static class RewritingVisitor extends IItpfVisitor.ItpfVisitorSkeleton<Integer> {

        private static final int CONFLUENCE_LIMIT = 1;
        private final IDPRuleAnalysis ruleAnalysis;
        private final int maxRewriteSteps;
        private final Abortion aborter;

        public RewritingVisitor(final IDPRuleAnalysis ruleAnalysis, final ApplicationMode mode, final int maxRewriteSteps, final Abortion aborter) {
            super(ItpfMark.ItpfRewriting, mode);
            this.ruleAnalysis = ruleAnalysis;
            this.maxRewriteSteps = maxRewriteSteps;
            this.aborter = aborter;
        }

        @Override
        public Itpf caseItp(final ItpfItp tp) {
            ItpRelation relation = tp.getRelation();
            final TRSTerm l = tp.getL();
            final TRSTerm r = tp.getR();
            if (relation == ItpRelation.TO_TRANS) {
                if (!l.unifies(r)) {
                    relation = ItpRelation.TO_PLUS;
                }
            }
            try {
                if (relation == ItpRelation.TO_PLUS && tp.getS().containsAll(l.getVariables()) &&
                tp.getS().containsAll(r.getVariables()) && this.ruleAnalysis.getQ().canBeRewritten(r)) {
                    final Set<GeneralizedRule> usableRules = this.ruleAnalysis.getUseableRules(null).getActive().keySet();
                    if (this.ruleAnalysis.getRAnalysis().getCriticalPairs(ImmutableCreator.create(usableRules)).isLocallyConfluent(RewritingVisitor.CONFLUENCE_LIMIT, this.aborter) == YNM.YES) {
                        for (final GeneralizedRule rule : usableRules) {
                            // l.rew
                        }
                    }
                }
            } catch (final AbortionException e) {
            }
            return this.mark(tp, tp);
        }


        @Override
        protected boolean checkVisit(final Itpf itpf) {
            if (this.applicationCount != 0 && this.mode == ApplicationMode.SingleStep) {
                return false;
            }
            final Integer rewriteSteps = itpf.getMark(this.mark);
            if (rewriteSteps != null && rewriteSteps < this.maxRewriteSteps) {
                return false;
            } else {
                return true;
            }
        }

        @Override
        protected Itpf mark(final Itpf origItpf, final Itpf newItpf) {
            if (this.mode == ApplicationMode.Multistep || origItpf.isAtom()) {
                if (newItpf != origItpf) {
                    final Integer rewriteSteps = origItpf.getMark(this.mark);
                    if (rewriteSteps == null) {
                        newItpf.setMark(this.mark, ItpfRewriting.ONE);
                    } else {
                        newItpf.setMark(this.mark, rewriteSteps + 1);
                    }
                } else {
                    newItpf.setMark(this.mark, ItpfRewriting.MAX_VALUE);
                }
            }
            return newItpf;
        }
}

}
