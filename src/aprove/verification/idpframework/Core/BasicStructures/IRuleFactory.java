package aprove.verification.idpframework.Core.BasicStructures;

import java.util.*;

import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class IRuleFactory {

    /**
     * creates a new UnconditionalIRule
     * @param l
     * @param r
     */
    public static UnconditionalIRule create(final IFunctionApplication<?> l,
        final ITerm<?> r) {
        return new UnconditionalIRule.Impl(l, r, null, null);
    }

    /**
     * creates a new UnconditionalIRule with known standard representation
     * @param l
     * @param r
     * @param lStd
     * @param rStd
     */
    public static UnconditionalIRule create(final IFunctionApplication<?> l,
        final ITerm<?> r,
        final IFunctionApplication<?> lStd,
        final ITerm<?> rStd) {
        return new UnconditionalIRule.Impl(l, r, lStd, rStd);
    }

    /**
     * creates a new ConditionalIRule
     * @param l
     * @param r
     * @param condition
     */
    public static ConditionalIRule create(final IFunctionApplication<?> l,
        final ITerm<?> r,
        final Itpf condition) {
        return new ConditionalIRule.Impl(l, r, condition, null, null, null);
    }

    /**
     * @param l left side of the rule
     * @param r right side of the rule
     * @param condition term that needs to be rewritten to TRUE
     * @param predefinedMap predefined semantics for the used symbols
     * @param itpfFactory factory used for the created formulas
     * @param allVarsInNF true iff all variables need to be in normal form
     *  (i.e., if you try to use this with higher-order stuff, you are screwed)
     * @return new rule l -> r, if condition != null it is l -> r | condition
     */
    public static IRule createWithExQuantifiedFreeVars(final IFunctionApplication<?> l,
        final ITerm<?> r,
        final ITerm<BooleanRing> condition,
        final IDPPredefinedMap predefinedMap,
        final ItpfFactory itpfFactory,
        final boolean allVarsInNF) {

        if (condition != null) {
            final ImmutableSet<ITerm<?>> vars;
            if (!allVarsInNF) {
                vars = ITerm.EMPTY_SET;
            } else {
                final Set<ITerm<?>> mutableVars =
                    new LinkedHashSet<ITerm<?>>();
                mutableVars.addAll(l.getVariables());
                mutableVars.addAll(r.getVariables());
                mutableVars.addAll(condition.getVariables());
                vars = ImmutableCreator.create(mutableVars);
            }

            final ItpfItp itp = itpfFactory.createItp(
                condition,
                null,
                null,
                ItpRelation.TO_TRANS,
                predefinedMap.getBooleanTrue().getTerm(),
                null,
                null);

            final Set<IVariable<?>> freeVariables = condition.getVariables();
            freeVariables.removeAll(l.getVariables());
            freeVariables.removeAll(r.getVariables());

            final ArrayList<ItpfQuantor> quantification = itpfFactory.createQuantors(
                freeVariables,
                itp.getVariables(),
                false);

            final Itpf newCondition = itpfFactory.create(
                ImmutableCreator.create(quantification),
                itp,
                true,
                vars);

            return IRuleFactory.create(l, r, newCondition);
        } else {
            return IRuleFactory.create(l, r);
        }

    }

    /**
     * creates a new ConditionalIRule with known standard representation
     * @param l
     * @param r
     * @param condition
     * @param lStd
     * @param rStd
     * @param conditionStd
     */
    public static ConditionalIRule create(final IFunctionApplication<?> l,
        final ITerm<?> r,
        final Itpf condition,
        final IFunctionApplication<?> lStd,
        final ITerm<?> rStd,
        final Itpf conditionStd) {
        return new ConditionalIRule.Impl(l, r, condition, lStd, rStd,
            conditionStd);
    }

    /**
     * Filters a rule map such that only uncponditional rules are retained
     * @param map
     * @return
     */
    public static <C extends Collection<? extends IRule>> Map<IFunctionSymbol<?>, Set<UnconditionalIRule>> retainUnconditional(final Map<IFunctionSymbol<?>, C> map) {
        final Map<IFunctionSymbol<?>, Set<UnconditionalIRule>> res =
            new LinkedHashMap<IFunctionSymbol<?>, Set<UnconditionalIRule>>();
        for (final Map.Entry<IFunctionSymbol<?>, C> entry : map.entrySet()) {
            final Set<UnconditionalIRule> collection =
                new LinkedHashSet<UnconditionalIRule>();
            for (final IRule rule : entry.getValue()) {
                if (rule.getCondition() == null) {
                    collection.add(rule.getUnconditionalRule());
                }
            }
            res.put(entry.getKey(), collection);
        }
        return res;
    }

}
