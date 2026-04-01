package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import java.util.*;

import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public interface BasicTermSubstitution extends IDPExportable, IBasicSubstitution {

    public boolean substitutesTerm(IVariable<?> v);
    public <D extends SemiRing<D>> ITerm<D> substituteTerm(IVariable<D> v);
    public boolean isEmpty();

    public ImmutableSet<IVariable<?>> getTermDomain();
    public ImmutableSet<IVariable<?>> getTermVariablesInCodomain();
    public ImmutableSet<IFunctionSymbol<?>> getFunctionSymbolsInCodomain();

    BasicTermSubstitution termCompose(BasicTermSubstitution sigma);

    public static abstract class BasicTermSubstitutionSkeleton<V extends ITerm<?>> extends
            AbstractSubstitution<IVariable<?>, V> implements BasicTermSubstitution {

        protected volatile ImmutableSet<IVariable<?>> cachedVarsCodomain;
        protected volatile ImmutableSet<IFunctionSymbol<?>> cachedFunctionSymbolsCodomain;

        protected BasicTermSubstitutionSkeleton(final ImmutableMap<IVariable<?>, ? extends V> map, final boolean cleanMap) {
            super(map, cleanMap);
        }

        @Override
        public boolean substitutesTerm(final IVariable<?> v) {
            return this.substitutes(v);
        }

        @SuppressWarnings("unchecked")
        @Override
        public <D extends SemiRing<D>> ITerm<D> substituteTerm(final IVariable<D> v) {
            return (ITerm<D>) this.substitute(v);
        }

        /**
         * returns the IVariable<?>s of the codomain(range) of this substitution
         */
        @Override
        public ImmutableSet<IVariable<?>> getTermVariablesInCodomain() {
            if (this.cachedVarsCodomain == null) {
                synchronized(this) {
                    if (this.cachedVarsCodomain == null) {
                        final Set<IVariable<?>> varsCodomain =
                            new LinkedHashSet<IVariable<?>>();
                        for (final Map.Entry<? extends IVariable<?>, ? extends ITerm<?>> entry : this.getMap().entrySet()) {
                            varsCodomain.addAll(entry.getValue().getVariables());
                        }
                        this.cachedVarsCodomain = ImmutableCreator.create(varsCodomain);
                    }
                }
            }
            return this.cachedVarsCodomain;
        }

        /**
         * returns the IVariable<?>s of the codomain(range) of this substitution
         */
        @Override
        public ImmutableSet<IFunctionSymbol<?>> getFunctionSymbolsInCodomain() {
            if (this.cachedFunctionSymbolsCodomain == null) {
                synchronized(this) {
                    if (this.cachedFunctionSymbolsCodomain == null) {
                        final Set<IFunctionSymbol<?>> functionSymbolsCodomain =
                            new LinkedHashSet<IFunctionSymbol<?>>();
                        for (final Map.Entry<? extends IVariable<?>, ? extends ITerm<?>> entry : this.getMap().entrySet()) {
                            functionSymbolsCodomain.addAll(entry.getValue().getFunctionSymbols());
                        }
                        this.cachedFunctionSymbolsCodomain = ImmutableCreator.create(functionSymbolsCodomain);
                    }
                }
            }
            return this.cachedFunctionSymbolsCodomain;
        }

        /**
         * note: a IVariable<?>-Renaming has to be injective !
         * @author Martin Pluecker, copied from Sebastian Weise
         */
        public boolean isVariableRenaming() {
            final Set<IVariable<?>> domain = new LinkedHashSet<IVariable<?>>();
            final Set<ITerm<?>> codomain = new LinkedHashSet<ITerm<?>>();
            for (final Map.Entry<? extends IVariable<?>, ? extends ITerm<?>> actVarTerm : this.getMap().entrySet()) {
                final IVariable<?> actVar = actVarTerm.getKey();
                final ITerm<?> actTerm = actVarTerm.getValue();
                if (!(actTerm instanceof IVariable<?>)) {
                    return false;
                }
                if (!actVar.getDomain().equals(actTerm.getDomain())) {
                    return false;
                }
                domain.add(actVar);
                codomain.add(actTerm);
            }
            if (domain.size() != codomain.size()) {
                return false;
            }
            return true;
        }

        /**
         * self-speaking method;
         * @author Martin Pluecker, copied from Sebastian Weise
         */
        public ImmutableSet<IVariable<?>> getVariables() {
            final Set<IVariable<?>> result =
                new LinkedHashSet<IVariable<?>>(this.getTermDomain());
            result.addAll(this.getTermVariablesInCodomain());
            return ImmutableCreator.create(result);
        }

        /**
         * returns the domain of this substitution
         */
        @Override
        public ImmutableSet<IVariable<?>> getTermDomain() {
            return ImmutableCreator.create(this.getMap().keySet());
        }

        /**
         * @return composed map or null if no changes are made to map
         */
        public static <V extends ITerm<?>> ImmutableMap<IVariable<?>, ITerm<?>> termCompose(final ImmutableMap<IVariable<?>, V> map, final BasicTermSubstitution sub) {
            boolean changed = false;
            final Map<IVariable<?>, ITerm<?>> newMap =
                new LinkedHashMap<IVariable<?>, ITerm<?>>();

            for (final Map.Entry<IVariable<?>, V> entry : map.entrySet()) {
                final IVariable<?> key = entry.getKey();
                final ITerm<?> value = entry.getValue();
                final ITerm<?> substResult = value.applySubstitution(sub);
                if (!substResult.equals(value)) {
                    changed = true;
                }

                if (!key.equals(substResult)) {
                    newMap.put(key, substResult);
                }
            }

            for (final IVariable<?> key : sub.getTermDomain()) {
                if (!map.containsKey(key)) {
                    changed = true;
                    newMap.put(key, sub.substituteTerm(key));
                }
            }

            if (changed) {
                return ImmutableCreator.create(newMap);
            } else {
                return null;
            }
        }

        @Override
        public boolean equals(final Object other) {
            if (this == other) {
                return true;
            }
            if (other instanceof BasicTermSubstitution) {
                final BasicTermSubstitution sigma = (BasicTermSubstitution) other;

                if (!this.getTermDomain().equals(sigma.getTermDomain())) {
                    return false;
                }

                for (final Map.Entry<IVariable<?>, ? extends V> entry : this.getMap().entrySet()) {
                    if (!entry.getValue().equals(sigma.substituteTerm(entry.getKey()))) {
                        return false;
                    }
                }
                return true;
            }
            return false;
        }

        @Override
        public int hashCode() {
            return this.getMap().hashCode();
        }

    }
}
