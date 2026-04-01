package aprove.verification.idpframework.Core.BasicStructures;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import immutables.*;

/**
 * A ConditionalIRule is a rule with an ITPF condition which must be staisfied
 * by he matcher which is applied to the lhs in order to perform a valid rewrite
 * step.
 * @author Martin Pluecker
 */
public interface ConditionalIRule extends IRule {

    public static class Impl extends IRule.IRuleSkeleton implements ConditionalIRule {

        protected Impl(final IFunctionApplication<?> l, final ITerm<?> r,
                final Itpf condition, final IFunctionApplication<?> stdL,
                final ITerm<?> stdR, final Itpf stdCondition) {
            super(l, r, condition, stdL, stdR, stdCondition);
            if (Globals.useAssertions) {
                assert (condition != null);
            }
        }

        /**
         * renames the Variables with given prefix and numbers starting from
         * STANDARD_NUMBER. E.g., for rule = f(x,y,x1,y) -> f(y,x,x,a) prefix =
         * x STANDARD_NUMBER = 0 we obtain f(x0,x1,x2,x1) -> f(x1,x0,x0,a). The
         * standard representation of a rule is
         * rule.getWithRenumberedVariables(STANDARD_PREFIX);
         * @param prefix
         * @return
         */
        @Override
        public ConditionalIRule getWithRenumberedVariables(final String prefix) {
            final Map<IVariable<?>, IVariable<?>> map =
                new HashMap<IVariable<?>, IVariable<?>>();
            final ImmutablePair<? extends IFunctionApplication<?>, Integer> numberedLAndInt =
                this.getLeft().renumberVariables(map, prefix, TRSTerm.STANDARD_NUMBER);

            final ImmutablePair<? extends ITerm<?>, Integer> numberedRAndInt =
                this.r.renumberVariables(map, prefix, numberedLAndInt.y);
            final Itpf numberedCondition =
                this.condition != null
                    ? this.condition.applySubstitution(VarRenaming.create(
                        ImmutableCreator.create(map), true, null)) : null;
            return new Impl(numberedLAndInt.x, numberedRAndInt.x,
                numberedCondition, this.stdL, this.stdR, this.stdCondition);
        }

        /**
         * returns a the standard representation of this rule where l = stdL and
         * r = stdR and condition = stdCondition. (constant time)
         * @see getWithRenumberedVariables
         */
        @Override
        public ConditionalIRule getStandardRepresentation() {
            // should be equivalent to getWithRenumberedVariables(STANDARD_PREFIX);
            return new Impl(this.stdL, this.stdR, this.condition, this.stdL,
                this.stdR, this.stdCondition);
        }

        @Override
        public UnconditionalIRule getUnconditionalRule() {
            throw new IllegalStateException(
                "Conditional rules always have a condition");
        }

        @Override
        public ConditionalIRule replaceAllFunctionSymbols(final FunctionSymbolReplacement replacementMap) {
            // TODO Auto-generated method stub
            final IFunctionApplication<?> replacedLeft =
                this.l.replaceAllFunctionSymbols(replacementMap);
            final ITerm<?> replacedRight =
                this.r.replaceAllFunctionSymbols(replacementMap);
            final Itpf replacedCond =
                this.condition.replaceAllFunctionSymbols(replacementMap);

            if (replacedLeft != this.l || replacedRight != this.r
                || replacedCond != this.condition) {
                return IRuleFactory.create(replacedLeft, replacedRight,
                    replacedCond);
            } else {
                return this;
            }
        }

    }
}
