package aprove.verification.idpframework.Core.Utility;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import immutables.*;

/**
 * @author MP
 */
public class ItpfUtil {

    public static boolean isExplicitelyQuantified(final List<ItpfQuantor> quantors, final IVariable<?> var) {
        for (int i = quantors.size() - 1; i >= 0; i--) {
            final ItpfQuantor quant = quantors.get(i);
            if (quant.getVariable().equals(var)) {
                return true;
            }
        }
        return false;
    }

    public static boolean isUniversalQuantified(final List<ItpfQuantor> quantors,
        final IVariable<?> var,
        final boolean implicitUniversalQuantification) {
        for (int i = quantors.size() - 1; i >= 0; i--) {
            final ItpfQuantor quant = quantors.get(i);
            if (quant.getVariable().equals(var)) {
                return quant.isUniversalQuantor();
            }
        }
        return implicitUniversalQuantification;
    }

    public static boolean isExistQuantified(final List<ItpfQuantor> quantors,
        final IVariable<?> var,
        final boolean outermost) {
        return ItpfUtil.<BigInt>isExistQuantified(null, quantors, var, outermost);
    }

    public static boolean isQuantified(final List<ItpfQuantor> quantors, final IVariable<?> var) {
        for (int i = quantors.size() - 1; i >= 0; i--) {
            final ItpfQuantor quant = quantors.get(i);
            if (quant.getVariable().equals(var)) {
                return true;
            }
        }

        return false;
    }

    public static <C extends SemiRing<C>> boolean isQuantified(final PolyInterpretation<C> polyInterpretation,
        final List<ItpfQuantor> quantors,
        final IVariable<?> var) {

        if (polyInterpretation.isExistQuantified(var)) {
            return true;
        }

        for (int i = quantors.size() - 1; i >= 0; i--) {
            final ItpfQuantor quant = quantors.get(i);
            if (quant.getVariable().equals(var)) {
                return true;
            }
        }

        return false;
    }

    public static <C extends SemiRing<C>> boolean isExistQuantified(final PolyInterpretation<C> polyInterpretation,
        final List<ItpfQuantor> quantors,
        final IVariable<?> var,
        final boolean outermost) {
        for (int i = quantors.size() - 1; i >= 0; i--) {
            final ItpfQuantor quant = quantors.get(i);
            if (quant.getVariable().equals(var)) {
                if (quant.isUniversalQuantor()) {
                    return false;
                } else if (!outermost) {
                    return true;
                } else {
                    for (int j = i - 1; j >= 0; j--) {
                        final ItpfQuantor outerQuant = quantors.get(j);
                        if (outerQuant.isUniversalQuantor()) {
                            return false;
                        }
                    }
                    return true;
                }
            }
        }

        if (polyInterpretation != null && var instanceof IVariable<?> && polyInterpretation.isExistQuantified(var)) {
            return true;
        }

        return false;
    }

    public static <C extends SemiRing<C>> boolean isUniversalQuantified(final PolyInterpretation<C> polyInterpretation,
        final List<ItpfQuantor> quantors,
        final IVariable<C> var,
        final boolean implicitUniversalQuantification) {
        if (ItpfUtil.isUniversalQuantified(quantors, var, false)) {
            return true;
        }

        if (!polyInterpretation.isExistQuantified(var)) {
            return implicitUniversalQuantification;
        }

        return false;
    }

    public static ImmutableList<ItpfQuantor> mergeQuantors(final ImmutableList<ItpfQuantor> quantification,
        final List<ItpfQuantor> newQuantors) {
        if (!quantification.isEmpty()) {
            if (!newQuantors.isEmpty()) {
                final ArrayList<ItpfQuantor> merged = new ArrayList<ItpfQuantor>(quantification);
                merged.addAll(newQuantors);
                return ImmutableCreator.create(merged);
            } else {
                return quantification;
            }
        } else if (!newQuantors.isEmpty()) {
            return ImmutableCreator.create(newQuantors);
        } else {
            return ItpfFactory.EMPTY_QUANTORS;
        }
    }

    public static ImmutableList<ItpfQuantor> cleanupQuantors(final List<ItpfQuantor> quantification) {
        return ItpfUtil.cleanupQuantors(quantification, null);
    }

    /**
     * @param quantification
     * @param usedVariables null represents the set of all variables
     * @return
     */
    public static ImmutableList<ItpfQuantor> cleanupQuantors(final List<ItpfQuantor> quantification,
        final Set<IVariable<?>> usedVariables) {
        if (quantification.isEmpty()) {
            return ItpfFactory.EMPTY_QUANTORS;
        } else {
            final Map<IVariable<?>, ItpfQuantor> quantified = new LinkedHashMap<>();

            for (final ItpfQuantor quantor : quantification) {
                if (usedVariables == null || usedVariables.contains(quantor.getVariable())) {
                    /*
                     * FIXME
                     * The following line does not make sense. quantified contains keys of type IVariable<?>
                     * but we try to remove a key of type ItpfQuantor (which could be a value?)
                     */
                    // quantified.remove(quantor);
                    quantified.put(quantor.getVariable(), quantor);
                }
            }

            final ArrayList<ItpfQuantor> newQuantors = new ArrayList<>(quantified.values());

            return ImmutableCreator.create(newQuantors);
        }
    }

    public static Set<ITerm<?>> expandS(final Set<ITerm<?>> s) {
        final LinkedHashSet<ITerm<?>> res = new LinkedHashSet<ITerm<?>>();

        for (final ITerm<?> sTerm : s) {
            sTerm.collectSubTerms(res, false);
        }

        return res;
    }

    public static List<ItpfQuantor> invertQuantors(final ItpfFactory itpfFactory,
        final ImmutableList<ItpfQuantor> quantification) {
        final ArrayList<ItpfQuantor> inverted = new ArrayList<ItpfQuantor>(quantification.size());
        for (final ItpfQuantor quantor : quantification) {
            inverted.add(itpfFactory.createQuantor(!quantor.isUniversalQuantor(), quantor.getVariable()));
        }

        return inverted;
    }

    public static Set<IVariable<?>> collectBoundVariables(final ImmutableList<ItpfQuantor> quantification) {
        final Set<IVariable<?>> bound = new LinkedHashSet<IVariable<?>>();
        for (final ItpfQuantor quantor : quantification) {
            bound.add(quantor.getVariable());
        }
        return bound;
    }

    public static VarRenaming getVariableRenaming(final PolyFactory polyFactory,
        final Set<IVariable<?>> variables,
        final FreshVarGenerator freshNames) {
        final Map<IVariable<?>, IVariable<?>> subst = new LinkedHashMap<IVariable<?>, IVariable<?>>();
        for (final IVariable<?> v : variables) {
            final String newName = freshNames.getFreshVariableName(v.getName(), false);
            if (!newName.equals(v.getName())) {
                subst.put(v, ITerm.createVariable(newName, v.getDomain()));
            }
        }
        return VarRenaming.create(ImmutableCreator.create(subst), true, polyFactory);
    }

}
