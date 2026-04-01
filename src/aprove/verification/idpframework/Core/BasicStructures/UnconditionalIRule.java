package aprove.verification.idpframework.Core.BasicStructures;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import immutables.*;

/**
 * An UnconditionalIRule is an IRule which is unconditional by construction.
 * @author Martin Pluecker
 */
public interface UnconditionalIRule extends IRule {

    public static class Impl extends IRule.IRuleSkeleton implements
            UnconditionalIRule {

        Impl(final IFunctionApplication<?> l, final ITerm<?> r,
                final IFunctionApplication<?> stdL, final ITerm<?> stdR) {
            super(l, r, null, stdL, stdR, null);
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
        public UnconditionalIRule getWithRenumberedVariables(final String prefix) {
            final Map<IVariable<?>, IVariable<?>> map =
                new HashMap<IVariable<?>, IVariable<?>>();

            final ImmutablePair<? extends IFunctionApplication<?>, Integer> numberedLAndInt =
                this.getLeft().renumberVariables(map, prefix, TRSTerm.STANDARD_NUMBER);

            final ImmutablePair<? extends ITerm<?>, Integer> numberedRAndInt =
                this.r.renumberVariables(map, prefix, numberedLAndInt.y);

            return new Impl(numberedLAndInt.x, numberedRAndInt.x, this.stdL,
                this.stdR);
        }

        /**
         * returns a the standard representation of this rule where l = stdL and
         * r = stdR (constant time)
         * @see getWithRenumberedVariables
         */
        @Override
        public UnconditionalIRule getStandardRepresentation() {
            // should be equivalent to getWithRenumberedVariables(STANDARD_PREFIX);
            return new Impl(this.stdL, this.stdR, this.stdL, this.stdR);
        }

        @Override
        public UnconditionalIRule getUnconditionalRule() {
            return this;
        }

        @Override
        public UnconditionalIRule replaceAllFunctionSymbols(final FunctionSymbolReplacement replacementMap) {
            // TODO Auto-generated method stub
            final IFunctionApplication<?> replacedLeft =
                this.l.replaceAllFunctionSymbols(replacementMap);
            final ITerm<?> replacedRight =
                this.r.replaceAllFunctionSymbols(replacementMap);
            if (replacedLeft != this.l || replacedRight != this.r) {
                return IRuleFactory.create(replacedLeft, replacedRight);
            } else {
                return this;
            }
        }

    }

}
