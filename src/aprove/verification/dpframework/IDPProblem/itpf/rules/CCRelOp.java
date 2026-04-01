package aprove.verification.dpframework.IDPProblem.itpf.rules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Docu-guess (fuhs):
 * Lifts "s rel t ->^(...) TRUE/FALSE" to "s rel' t" or "t rel' s"
 * for suitable rel', where the additional requirements on the
 * usable rules of s and t are included as well.
 *
 * @author mpluecke
 */
public class CCRelOp extends IItpfRule.ItpfRuleSkeleton {

    private ExportableString longDescription;
    private ExportableString shortDescription;

    public CCRelOp() {
        this.shortDescription = this.longDescription = new ExportableString("CCRelOp");
    }


    @Override
    public Exportable getDescription(NameLength length) {
        switch (length) {
        case SHORT :
            return this.shortDescription;
        case LONG :
            return this.longDescription;
        }
        return null;
    }


    @Override
    public boolean isApplicable(IDPProblem idp) {
        return true;
    }

    @Override
    public boolean isApplicable(IDPProblem idp, Itpf formula, ApplicationMode mode) {
        return true;
    }


    @Override
    public Itpf process(IDPProblem idp, Itpf formula, ApplicationMode mode,
            Abortion aborter) throws AbortionException {
        CCRelOpVisitor visitor = new CCRelOpVisitor(idp.getRuleAnalysis(), mode);
        return visitor.applyTo(formula.normalize());
    }

    protected static class CCRelOpVisitor extends IItpfVisitor.ItpfVisitorSkeleton<Object> {

        private final IDPRuleAnalysis ruleAnalysis;
        private final IDPPredefinedMap preDefineds;

        public CCRelOpVisitor(IDPRuleAnalysis ruleAnalysis, ApplicationMode mode) {
            super(ItpfMark.CCRelOp, mode);
            this.ruleAnalysis = ruleAnalysis;
            this.preDefineds = ruleAnalysis.getPreDefinedMap();
        }

        @Override
        public boolean fcaseNeg(ItpfNeg neg) {
            return false;
        }

        @Override
        public Itpf caseItp(final ItpfItp tp) {
            if (tp.getRelation().isRewriteRel() && tp.getKLeft() == null && tp.getKRight() == null) {
                TRSTerm l = tp.getL();
                TRSTerm r = tp.getR();
                if (!l.isVariable() && !r.isVariable()) {
                    TRSFunctionApplication fl = (TRSFunctionApplication) l;
                    TRSFunctionApplication fr = (TRSFunctionApplication) r;
                    if (this.preDefineds.isBooleanTrue(fr.getRootSymbol())) {
                        @SuppressWarnings("unchecked")
                        Set<? extends TRSTerm> sVars =
                            (Set<? extends TRSTerm>)
                                aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(tp.getS());
                        if (this.ruleAnalysis.isNfQSubsetEqNfR() && sVars.containsAll(l.getVariables())) {
                            FunctionSymbol leftRoot = fl.getRootSymbol();
                            PredefinedFunction<? extends Domain> function =
                                this.preDefineds.getPredefinedFunction(leftRoot);
                            TRSTerm ll = fl.getArgument(0);
                            TRSTerm lr = fl.getArgument(1);
                            switch(function.getFunc()) {
                            case Ge:
                                return this.mark(tp, this.transformToAbstractRel(ll, lr, true, tp.getS()));
                            case Gt:
                                return this.mark(tp, this.transformToAbstractRel(ll, lr, false, tp.getS()));
                            case Le:
                                return this.mark(tp, this.transformToAbstractRel(lr, ll, true, tp.getS()));
                            case Lt:
                                return this.mark(tp, this.transformToAbstractRel(lr, ll, false, tp.getS()));
                            case Eq:
                                return this.mark(tp, ItpfAnd.create(
                                        this.mark(tp, this.transformToAbstractRel(ll, lr, true, tp.getS())),
                                        this.mark(tp, this.transformToAbstractRel(lr, ll, true, tp.getS()))
                                        ));
                            case Neq:
                                return this.mark(tp, ItpfOr.create(
                                        this.mark(tp, this.transformToAbstractRel(ll, lr, false, tp.getS())),
                                        this.mark(tp, this.transformToAbstractRel(lr, ll, false, tp.getS()))
                                        ));
                            }
                        }
                    } else if (this.preDefineds.isBooleanFalse(fr.getRootSymbol())) {
                        @SuppressWarnings("unchecked")
                        Set<? extends TRSTerm> sVars =
                            (Set<? extends TRSTerm>)
                                aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(tp.getS());
                        if (this.ruleAnalysis.isNfQSubsetEqNfR() && sVars.containsAll(l.getVariables())) {
                            FunctionSymbol leftRoot = fl.getRootSymbol();
                            PredefinedFunction<? extends Domain> function =
                                this.preDefineds.getPredefinedFunction(leftRoot);
                            TRSTerm ll = fl.getArgument(0);
                            TRSTerm lr = fl.getArgument(1);
                            switch(function.getFunc()) {
                            case Ge:
                                return this.mark(tp, this.transformToAbstractRel(lr, ll, false, tp.getS()));
                            case Gt:
                                return this.mark(tp, this.transformToAbstractRel(lr, ll, true, tp.getS()));
                            case Le:
                                return this.mark(tp, this.transformToAbstractRel(ll, lr, false, tp.getS()));
                            case Lt:
                                return this.mark(tp, this.transformToAbstractRel(ll, lr, true, tp.getS()));
                            case Eq:
                                return this.mark(tp, ItpfOr.create(
                                        this.mark(tp, this.transformToAbstractRel(ll, lr, false, tp.getS())),
                                        this.mark(tp, this.transformToAbstractRel(lr, ll, false, tp.getS()))
                                        ));
                            case Neq:
                                return this.mark(tp, ItpfAnd.create(
                                        this.mark(tp, this.transformToAbstractRel(ll, lr, true, tp.getS())),
                                        this.mark(tp, this.transformToAbstractRel(lr, ll, true, tp.getS()))
                                        ));
                            }
                        }
                    }
                }
            }
            return this.mark(tp, tp);
        }

        /**
         *
         * @param l
         * @param r
         * @param ge true iff l >= r, false iff l > r
         * @param S
         * @return
         */
        protected Itpf transformToAbstractRel(TRSTerm l, TRSTerm r, boolean ge, ImmutableSet<TRSTerm> S) {
            return ItpfAnd.create(
                    ItpfItp.create(l,
                            RelDependency.Increasing, ItpfItp.EMPTY_CONTEXT,
                            ge ? ItpRelation.ABSTRACT_GE : ItpRelation.ABSTRACT_GT,
                            r, RelDependency.Decreasing, ItpfItp.EMPTY_CONTEXT,
                            S),
                    ItpfUra.create(
                            this.ruleAnalysis.getUseableRulesEstimation(null),
                            RelDependency.Increasing, l,
                            ItpRelation.ABSTRACT_GE),
                    ItpfUra.create(
                            this.ruleAnalysis.getUseableRulesEstimation(null),
                            RelDependency.Decreasing, r,
                            ItpRelation.ABSTRACT_GE));
        }


    }

}
