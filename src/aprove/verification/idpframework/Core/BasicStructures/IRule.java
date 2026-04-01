package aprove.verification.idpframework.Core.BasicStructures;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * An IRule is a pair of terms where the lhs may be no IVariable<?> but there is no
 * restriction on the set of Variables of the rhs (compare to standard rewrite
 * rule). Moreover the rule may be annotated with a condition. This ITPF
 * condition (if present) must be staisfied by he matcher which is applied to
 * the lhs in order to perform a valid rewrite step.
 * @author Martin Pluecker
 */
public interface IRule extends Immutable, Exportable, IDPExportable, Comparable<IRule> {

    /**
     * returns the lhs
     */
    public IFunctionApplication<?> getLeft();

    /**
     * returns the rhs.
     */
    public ITerm<?> getRight();

    /**
     * returns the condition
     */
    public Itpf getCondition();

    /**
     * returns the condition in standard representation
     */
    public Itpf getStdCondition();

    /**
     * returns the set of terms occurring in this rule, i.e. {l,r}
     */
    public Set<ITerm<?>> getTerms();

    /**
     * returns the set of Variables occurring in this rule
     */
    public Set<IVariable<?>> getVariables();

    /**
     * returns the set of Variables occurring on the rhs but not on the lhs.
     */
    public Set<IVariable<?>> getUnboundedVariables();

    /**
     * returns the set of IFunctionSymbol<?>s occurring in this rule. the resulting
     * set may be modified
     */
    public Set<IFunctionSymbol<?>> getFunctionSymbols();

    /**
     * returns the root symbol of this rule, i.e. the root symbol of the lhs.
     */
    public IFunctionSymbol<?> getRootSymbol();

    /**
     * renames the Variables with given prefix and numbers starting from
     * STANDARD_NUMBER. E.g., for rule = f(x,y,x1,y) -> f(y,x,x,a) prefix = x
     * STANDARD_NUMBER = 0 we obtain f(x0,x1,x2,x1) -> f(x1,x0,x0,a). The
     * standard representation of a rule is
     * rule.getWithRenumberedVariables(STANDARD_PREFIX);
     * @param prefix
     * @return
     */
    public IRule getWithRenumberedVariables(String prefix);

    /**
     * returns the lhs in standardRepresentation. (constant time)
     */
    public IFunctionApplication<?> getLhsInStandardRepresentation();

    /**
     * returns the rhs in standardRepresentation. (constant time)
     */
    public ITerm<?> getRhsInStandardRepresentation();

    /**
     * Replace all function symbols according to given replacement map
     * @param replacementMap The replacement.
     * @return
     */
    public IRule replaceAllFunctionSymbols(final FunctionSymbolReplacement replacementMap);

    /**
     * returns a the standard representation of this rule where l = stdL and r =
     * stdR. (constant time)
     * @see getWithRenumberedVariables
     */
    public IRule getStandardRepresentation();

    /**
     * Operation only valid, if condition is null
     * @return
     */
    public UnconditionalIRule getUnconditionalRule();

    /**
     * @return Rule after applying the substitution (constant time)
     */
    public IRule applySubstitution(final PolyTermSubstitution sigma);

    public static abstract class IRuleSkeleton implements IRule {

        /*
         * real values
         */
        protected final IFunctionApplication<?> l;
        protected final ITerm<?> r;

        protected final Itpf condition;

        /*
         * computed values
         */
        protected final IFunctionApplication<?> stdL;
        protected final ITerm<?> stdR;
        protected final Itpf stdCondition;

        // protected final Set<IVariable<?>> domainedVariables;

        protected final int hashCode;

        private static boolean checkProperLandR(final IFunctionApplication<?> l, final ITerm<?> r) {
            return l != null && r != null;
        }

        private static boolean checkProperStd(
            final IFunctionApplication<?> l,
            final IFunctionApplication<?> stdL,
            final Itpf condition,
            final ITerm<?> r,
            final ITerm<?> stdR,
            final Itpf stdCondition)
        {
            if (stdL == null || stdR == null) {
                return false;
            }
            final Map<IVariable<?>, IVariable<?>> map = new HashMap<IVariable<?>, IVariable<?>>();
            final ImmutablePair<? extends IFunctionApplication<?>, Integer> stdLAndInt =
                l.renumberVariables(map, TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
            if (!stdLAndInt.x.equals(stdL)) {
                return false;
            }
            final ImmutablePair<? extends ITerm<?>, Integer> stdRAndInt =
                r.renumberVariables(map, TRSTerm.STANDARD_PREFIX, stdLAndInt.y);
            if (!stdRAndInt.x.equals(stdR)) {
                System.err.println(l
                    + " -> "
                    + r
                    + " --- >>> "
                    + stdLAndInt.x
                    + " -> "
                    + stdRAndInt.x
                    + " -- >> "
                    + stdR
                    + " / "
                    + map);
            }
            if (!stdRAndInt.x.equals(stdR)) {
                return false;
            }
            if (stdCondition != null
                && !stdCondition.equals(stdCondition.applySubstitution(VarRenaming.create(
                    ImmutableCreator.create(map),
                    true,
                    null))))
            {
                return false;
            }
            return true;
        }

        /**
         * creates a new generalized rule. Restrictions: neither l nor r may be
         * null
         * @param l - a term
         * @param r - a term
         */
        IRuleSkeleton(
            final IFunctionApplication<?> l,
            final ITerm<?> r,
            final Itpf condition,
            IFunctionApplication<?> stdL,
            ITerm<?> stdR,
            Itpf stdCondition)
        {
            this.l = l;
            this.r = r;
            this.condition = condition;
            /*
            this.domainedVariables = new LinkedHashSet<IVariable<?>>();
            for (final IVariable<?> var : getVariables()) {
                if (!var.getDomain().equals(DomainFactory.UNKNOWN)) {
                    domainedVariables.add(var);
                }
            }*/
            if (Globals.useAssertions) {
                assert (IRuleSkeleton.checkProperLandR(l, r));
                if (condition != null) {
                    assert (this.getVariables().containsAll(condition.getFreeVariables()));
                }
                assert ((stdL == null && stdR == null) || (stdL != null && stdR != null));
                assert ((condition == null && stdCondition == null))
                    || (condition != null && (stdL == null && stdCondition == null || stdL != null
                        && stdCondition != null));
                final Map<String, IVariable<?>> vars = new HashMap<String, IVariable<?>>();
                for (final IVariable<?> var : this.getVariables()) {
                    final IVariable<?> old = vars.put(var.getName(), var);
                    assert (old == null || old.equals(var)) : "variable name clash: " + var.getName();

                }
            }
            if (stdL == null) {
                final Map<IVariable<?>, IVariable<?>> map = new HashMap<IVariable<?>, IVariable<?>>();
                final ImmutablePair<? extends IFunctionApplication<?>, Integer> stdLAndInt =
                    l.renumberVariables(map, TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
                final ImmutablePair<? extends ITerm<?>, Integer> stdRAndInt =
                    r.renumberVariables(map, TRSTerm.STANDARD_PREFIX, stdLAndInt.y);
                if (condition != null) {
                    stdCondition =
                        condition.applySubstitution(VarRenaming.create(ImmutableCreator.create(map), false, null));
                }
                stdL = stdLAndInt.x;
                stdR = stdRAndInt.x;
            } else {
                if (Globals.useAssertions) {
                    assert (IRuleSkeleton.checkProperStd(this.l, stdL, condition, this.r, stdR, stdCondition));
                }
            }
            this.stdL = stdL;
            this.stdR = stdR;
            this.stdCondition = stdCondition;
            this.hashCode =
                490321
                    * stdL.hashCode()
                    + 12812
                    * stdR.hashCode()
                    + 312038193
                    + (stdCondition != null ? stdCondition.hashCode() * 31 : 0);
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#hashCode()
         */
        @Override
        public int hashCode() {
            return this.hashCode;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#equals(java.lang.Object)
         */
        @Override
        /**
         * Equality is defined modulo IVariable<?> renaming.
         *
         * In the impl. this is done using a standard representation of a rule
         */
        /*
         * if you remove the final and define some other kind
         * of equality for the children class, please
         * make sure that compareTo is also updated accordingly!!
         */
        public final boolean equals(final Object other) {
            if (this == other) {
                return true;
            }
            if (other instanceof IRule) {
                final IRule rule = (IRule) other;
                return this.hashCode == rule.hashCode()
                    && this.stdL.equals(rule.getLhsInStandardRepresentation())
                    && this.stdR.equals(rule.getRhsInStandardRepresentation());
            }
            return false;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#compareTo(aprove.verification.idpframework.Core.BasicStructures.IRule)
         */
        @Override
        public final int compareTo(final IRule other) {
            int compare = this.stdL.compareTo(other.getLhsInStandardRepresentation());
            if (compare == 0) {
                compare = this.stdR.compareTo(other.getRhsInStandardRepresentation());
            }
            return compare;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getLeft()
         */
        @Override
        public IFunctionApplication<?> getLeft() {
            return this.l;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getRight()
         */
        @Override
        public ITerm<?> getRight() {
            return this.r;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getCondition()
         */
        @Override
        public Itpf getCondition() {
            return this.condition;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getStdCondition()
         */
        @Override
        public Itpf getStdCondition() {
            return this.stdCondition;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getTerms()
         */
        @Override
        public Set<ITerm<?>> getTerms() {
            final Set<ITerm<?>> res = new LinkedHashSet<ITerm<?>>();
            res.add(this.l);
            res.add(this.r);
            return res;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getVariables()
         */
        @Override
        public Set<IVariable<?>> getVariables() {
            final Set<IVariable<?>> vars = new LinkedHashSet<IVariable<?>>(this.l.getVariables());
            vars.addAll(this.r.getVariables());
            return vars;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getUnboundedVariables()
         */
        @Override
        public Set<IVariable<?>> getUnboundedVariables() {
            final Set<IVariable<?>> vars = new LinkedHashSet<IVariable<?>>(this.r.getVariables());
            vars.removeAll(this.l.getVariables());
            return vars;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getFunctionSymbols()
         */
        @Override
        public Set<IFunctionSymbol<?>> getFunctionSymbols() {
            final Set<IFunctionSymbol<?>> fs = new LinkedHashSet<IFunctionSymbol<?>>();
            this.l.collectFunctionSymbols(fs);
            this.r.collectFunctionSymbols(fs);
            if (this.condition != null) {
                fs.addAll(this.condition.getFunctionSymbols());
            }
            return fs;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getRootSymbol()
         */
        @Override
        public IFunctionSymbol<?> getRootSymbol() {
            return this.getLeft().getRootSymbol();
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getWithRenumberedVariables(java.lang.String)
         */
        @Override
        public abstract IRule getWithRenumberedVariables(String prefix);

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getLhsInStandardRepresentation()
         */
        @Override
        public IFunctionApplication<?> getLhsInStandardRepresentation() {
            return this.stdL;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getRhsInStandardRepresentation()
         */
        @Override
        public ITerm<?> getRhsInStandardRepresentation() {
            return this.stdR;
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#applySubstitution()
         */
        @Override
        public IRule applySubstitution(final PolyTermSubstitution sigma) {
            if (sigma.isEmpty()) {
                return this;
            }
            return IRuleFactory.create(this.l.applySubstitution(sigma), this.r.applySubstitution(sigma), this.condition != null
                ? this.condition.applySubstitution(sigma)
                    : null);
        }

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#getStandardRepresentation()
         */
        @Override
        public abstract IRule getStandardRepresentation();

        /* (non-Javadoc)
         * @see aprove.verification.idpframework.Core.BasicStructures.IRule#replaceAllFunctionSymbols()
         */
        @Override
        public abstract IRule replaceAllFunctionSymbols(final FunctionSymbolReplacement replacementMap);

        public static
            Map<IFunctionSymbol<?>, Set<IFunctionApplication<?>>>
            computeLhsOfRulesAsMapInStandardRepresentation(
                final Map<IFunctionSymbol<?>, ? extends Set<? extends IRule>> ruleMap)
        {
            final Map<IFunctionSymbol<?>, Set<IFunctionApplication<?>>> res =
                new LinkedHashMap<IFunctionSymbol<?>, Set<IFunctionApplication<?>>>();
            for (final Map.Entry<IFunctionSymbol<?>, ? extends Set<? extends IRule>> entry : ruleMap.entrySet()) {
                final Set<IFunctionApplication<?>> lhss = new LinkedHashSet<IFunctionApplication<?>>();
                for (final IRule rule : entry.getValue()) {
                    lhss.add(rule.getLhsInStandardRepresentation());
                }
                res.put(entry.getKey(), lhss);
            }
            return res;
        }

        @Override
        public final String toString() {
            return this.export(new PLAIN_Util());
        }

        @Override
        public final String export(final Export_Util o) {
            return this.export(o, IDPExportable.DEFAULT_LEVEL);
        }

        @Override
        public final String export(final Export_Util o, final VerbosityLevel verbosityLevel) {
            final StringBuilder sb = new StringBuilder();
            this.export(sb, o, verbosityLevel);
            return sb.toString();
        }

        @Override
        public void export(final StringBuilder sb, final Export_Util o, final VerbosityLevel verbosityLevel) {
            sb.append(this.getLeft().export(o));
            sb.append(" ");
            sb.append(o.rightarrow());
            sb.append(" ");
            sb.append(this.getRight().export(o));
            /*
            if (!domainedVariables.isEmpty()
                    && level.compareTo(VerbosityLevel.MIDDLE) >= 0) {
                sb.append(eu.escape(" ["));
                final Iterator<IVariable<?>> domainedIter = domainedVariables.iterator();
                while (domainedIter.hasNext()) {
                    final IVariable<?> domained = domainedIter.next();
                    sb.append(domained.export(eu));
                    sb.append(":");
                    sb.append(domained.export(eu));
                    if (domainedIter.hasNext()) {
                        sb.append(", ");
                    }
                }
                sb.append(eu.escape("]"));
            }
             */
            if (this.condition != null && !this.condition.isTrue()) {
                sb.append(o.escape(" | "));
                this.condition.export(sb, o, verbosityLevel);
            }
        }

    }

}
