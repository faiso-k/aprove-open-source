package aprove.verification.idpframework.Core.BasicStructures.Substitutions;


import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class NonBoundPolyTermSubstitution extends IBasicSubstitution.IBasicSubstitutionSkeleton implements PolyTermSubstitution {

    public static NonBoundPolyTermSubstitution create(final PolyTermSubstitution sigma, final ImmutableCollection<IVariable<?>> boundKeys) {
        if (sigma instanceof NonBoundPolyTermSubstitution) {
            final NonBoundPolyTermSubstitution nonBound = (NonBoundPolyTermSubstitution) sigma;
            if (nonBound.getBoundKeys().equals(boundKeys)) {
                return nonBound;
            }
        }

        return new NonBoundPolyTermSubstitution(sigma, boundKeys);
    }

    private final PolyTermSubstitution sigma;
    private final ImmutableCollection<IVariable<?>> boundKeys;
    private volatile ImmutableSet<IVariable<?>> cachedVarsCodomain;
    private volatile ImmutableSet<IFunctionSymbol<?>> cachedFunctionSymbolsCodomain;

    private NonBoundPolyTermSubstitution(final PolyTermSubstitution sigma, final ImmutableCollection<IVariable<?>> boundKeys) {
        this.sigma = sigma;
        this.boundKeys = boundKeys;
    }

    @Override
    public boolean substitutesTerm(final IVariable<?> v) {
        return !this.boundKeys.contains(v) && this.sigma.substitutesTerm(v);
    }

    @Override
    public boolean substitutesPoly(final PolyVariable<?> v) {
        return !this.boundKeys.contains(v) && this.sigma.substitutesPoly(v);
    }

    @Override
    public boolean substitutesPoly(final Collection<? extends PolyVariable<?>> vs) {
        for (final PolyVariable<?> var : vs) {
            if (this.substitutesPoly(var)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public <D extends SemiRing<D>> ITerm<D> substituteTerm(final IVariable<D> v) {
        if (this.boundKeys.contains(v)) {
            return null;
        } else {
            return this.sigma.substituteTerm(v);
        }
    }

    @Override
    public <C extends SemiRing<C>> Polynomial<C> substitutePoly(final PolyVariable<C> v) {
        if (this.boundKeys.contains(v)) {
            return null;
        } else {
            return this.sigma.substitutePoly(v);
        }
    }

    @Override
    public boolean isEmpty() {
        return this.sigma.isEmpty() ||
            this.boundKeys.containsAll(this.sigma.getTermDomain()) &&
            this.boundKeys.containsAll(this.sigma.getPolyDomain());
    }

    @Override
    public ImmutableSet<IVariable<?>> getTermDomain() {
        final LinkedHashSet<IVariable<?>> domain = new LinkedHashSet<IVariable<?>>(this.sigma.getTermDomain());
        domain.removeAll(this.boundKeys);
        return ImmutableCreator.create(domain);
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

                    for (final IVariable<?> var : this.sigma.getTermDomain()) {
                        if (!this.boundKeys.contains(var)) {
                            varsCodomain.addAll(this.sigma.substituteTerm(var).getVariables());
                        }
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

                    for (final IVariable<?> var : this.sigma.getTermDomain()) {
                        if (!this.boundKeys.contains(var)) {
                            functionSymbolsCodomain.addAll(this.sigma.substituteTerm(var).getFunctionSymbols());
                        }
                    }
                    this.cachedFunctionSymbolsCodomain = ImmutableCreator.create(functionSymbolsCodomain);
                }
            }
        }
        return this.cachedFunctionSymbolsCodomain;
    }

    @Override
    public Set<? extends PolyVariable<?>> getPolyDomain() {
        final LinkedHashSet<PolyVariable<?>> domain = new LinkedHashSet<PolyVariable<?>>(this.sigma.getPolyDomain());
        domain.removeAll(this.boundKeys);
        return domain;
    }

    public ImmutableCollection<IVariable<?>> getBoundKeys() {
        return this.boundKeys;
    }

    @Override
    public PolyTermSubstitution termCompose(final BasicTermSubstitution sigma) {
        final PolyTermSubstitution newSigma = this.sigma.polyTermCompose(sigma);
        if (newSigma != this.sigma) {
            return NonBoundPolyTermSubstitution.create(newSigma, this.boundKeys);
        } else {
            return this;
        }
    }

    @Override
    public PolyTermSubstitution polyCompose(final BasicPolySubstitution sigma) {
        final PolyTermSubstitution newSigma = this.sigma.polyCompose(sigma);
        if (newSigma != this.sigma) {
            return NonBoundPolyTermSubstitution.create(newSigma, this.boundKeys);
        } else {
            return this;
        }
    }

    @Override
    public PolyTermSubstitution compose(final PolyTermSubstitution sigma) {
        final PolyTermSubstitution newSigma = this.sigma.polyCompose(sigma);
        if (newSigma != this.sigma) {
            return NonBoundPolyTermSubstitution.create(newSigma, this.boundKeys);
        } else {
            return this;
        }
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        this.sigma.export(sb, eu, verbosityLevel);
    }

    @Override
    public Set<?> getDomain() {
        final LinkedHashSet<Object> domain = new LinkedHashSet<Object>(this.sigma.getDomain());
        domain.removeAll(this.boundKeys);
        return domain;
    }

    @Override
    public Object substitute(final Object key) {
        if (this.boundKeys.contains(key)) {
            return null;
        } else {
            return this.sigma.substitute(key);
        }
    }

    @Override
    public PolyTermSubstitution polyTermCompose(final BasicTermSubstitution sigma) {
        return this.termCompose(sigma);
    }

}