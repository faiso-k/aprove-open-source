package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public abstract class AbstractTermToPolyTermSubstitution<I extends BasicTermSubstitution, O extends PolyTermSubstitution> extends IBasicSubstitution.IBasicSubstitutionSkeleton implements PolyTermSubstitution {

    protected final PolyInterpretation<?> polyInterpretation;
    protected final IDPPredefinedMap predefinedMap;
    protected final I sigma;
    private volatile ImmutableSet<PolyVariable<?>> polyDomain;

    protected AbstractTermToPolyTermSubstitution (
        final I sigma, final IDPPredefinedMap predefinedMap, final PolyInterpretation<?> interpretation) {
        this.predefinedMap = predefinedMap;
        this.polyInterpretation = interpretation;
        this.sigma = sigma;

        if (sigma == null) {
            throw new IllegalArgumentException("substitution sigma must not be null");
        }
    }

    @Override
    public boolean isEmpty() {
        return this.sigma.isEmpty();
    }

    @Override
    public boolean substitutesTerm(final IVariable<?> v) {
        return this.sigma.substitutesTerm(v);
    }

    @Override
    public <D extends SemiRing<D>> ITerm<D> substituteTerm(final IVariable<D> v) {
        return this.sigma.substituteTerm(v);
    }

    public IDPPredefinedMap getPredefinedMap() {
        return this.predefinedMap;
    }

    public PolyInterpretation<?> getPolyInterpretation() {
        return this.polyInterpretation;
    }

    @Override
    public ImmutableSet<IVariable<?>> getTermDomain() {
        return this.sigma.getTermDomain();
    }

    @Override
    public ImmutableSet<IVariable<?>> getTermVariablesInCodomain() {
        return this.sigma.getTermVariablesInCodomain();
    }

    @Override
    public ImmutableSet<IFunctionSymbol<?>> getFunctionSymbolsInCodomain() {
        return this.sigma.getFunctionSymbolsInCodomain();
    }

    @Override
    public boolean substitutesPoly(final PolyVariable<?> v) {
        if (!v.isMax()) {
            return this.sigma.substitutesTerm((IVariable<?>) v);
        } else {
            return false;
        }
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
    public Set<?> getDomain() {
        return this.sigma.getDomain();
    }

    @Override
    public Object substitute(final Object key) {
        return this.sigma.substitute(key);
    }

    @Override
    public <C extends SemiRing<C>> Polynomial<C> substitutePoly(final PolyVariable<C> v) {
        if (!v.isMax()) {
            if (this.polyInterpretation == null) {
                throw new UnsupportedOperationException("no poly interpretation given");
            }


            final IVariable<C> realVariable = (IVariable<C>) v;
            final ITerm<C> substTerm = this.sigma.substituteTerm(realVariable);

            assert realVariable.getRing().isSameRing(this.polyInterpretation.getRing()) : "ring clash";

            if (!PredefinedUtil.isPolynomialTerm(substTerm)) {
                throw new UnsupportedOperationException("non polynomial term: " + substTerm.export(new PLAIN_Util(), VerbosityLevel.HIGH));
            }

            @SuppressWarnings("unchecked")
            final
            Polynomial<C> result = (Polynomial<C>) this.polyInterpretation.interpretTerm(substTerm, RelDependency.Increasing);
            return result;
        }
        return null;
    }

    @Override
    public Set<PolyVariable<?>> getPolyDomain() {
        if (this.sigma instanceof Immutable) {
            if (this.polyDomain == null) {
                synchronized (this) {
                    if (this.polyDomain == null) {
                        this.polyDomain = this.createPolyDomain();
                    }
                }
            }
            return this.polyDomain;
        } else {
            return this.createPolyDomain();
        }
    }

    private ImmutableLinkedHashSet<PolyVariable<?>> createPolyDomain() {
        if (this.polyInterpretation == null) {
            throw new UnsupportedOperationException("no poly interpretation given");
        }

        final LinkedHashSet<PolyVariable<?>> dom =
            new LinkedHashSet<PolyVariable<?>>();

        for (final IVariable<?> var : this.sigma.getTermDomain()) {
            dom.add(var);
        }

        return ImmutableCreator.create(dom);
    }

    @Override
    public O compose(final PolyTermSubstitution sigma) {
        final I newSigma = (I) this.sigma.termCompose(sigma);
        if (newSigma != this.sigma) {
            return this.createNewInstance(newSigma, this.predefinedMap, this.polyInterpretation);
        } else {
            return (O) this;
        }
    }

    @Override
    public O termCompose(final BasicTermSubstitution sigma) {
        final I newSigma = (I) this.sigma.termCompose(sigma);
        if (newSigma != this.sigma) {
            return this.createNewInstance(newSigma, this.predefinedMap, this.polyInterpretation);
        } else {
            return (O) this;
        }
    }

    protected abstract O createNewInstance(I newSigma,
        IDPPredefinedMap predefinedMap,
        PolyInterpretation<?> polyInterpretation);

    @Override
    public O polyCompose(final BasicPolySubstitution sigma) {
        return this.compose(PolyToPolyTermSubstitution.create(sigma, this.predefinedMap, this.polyInterpretation));
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        this.sigma.export(sb, eu, verbosityLevel);
    }

}
