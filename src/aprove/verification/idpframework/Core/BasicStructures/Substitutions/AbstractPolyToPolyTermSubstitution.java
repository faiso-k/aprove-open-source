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
public abstract class AbstractPolyToPolyTermSubstitution<I extends BasicPolySubstitution, O extends PolyTermSubstitution> extends IBasicSubstitution.IBasicSubstitutionSkeleton implements PolyTermSubstitution {

    private final I sigma;
    private final IDPPredefinedMap predefinedMap;
    private final PolyInterpretation<?> polyInterpretation;

    private volatile ImmutableSet<IVariable<?>> termDomain;
    private volatile ImmutableSet<IVariable<?>> termVariablesCodomain;
    private volatile ImmutableSet<IFunctionSymbol<?>> functionSymbolsCodomain;

    protected AbstractPolyToPolyTermSubstitution (
            final I sigma, final IDPPredefinedMap predefinedMap, final PolyInterpretation<?> polyInterpretation) {
        this.predefinedMap = predefinedMap;
        this.polyInterpretation = polyInterpretation;
        this.sigma = sigma;
    }

    @Override
    public boolean isEmpty() {
        return this.sigma.isEmpty();
    }

    @Override
    public boolean substitutesTerm(final IVariable<?> v) {
        return this.sigma.getPolyDomain().contains(v);
    }

    @Override
    public <R extends SemiRing<R>> ITerm<R> substituteTerm(final IVariable<R> v) {
        final Polynomial<R> poly = this.sigma.substitutePoly(v);
        if (poly != null) {
            return poly.toTerm(this.predefinedMap);
        }
        return null;
    }

    public IDPPredefinedMap getPredefinedMap() {
        return this.predefinedMap;
    }

    public PolyInterpretation<?> getPolyInterpretation() {
        return this.polyInterpretation;
    }

    @Override
    public ImmutableSet<IVariable<?>> getTermDomain() {
        if (this.sigma instanceof Immutable) {
            if (this.termDomain == null) {
                synchronized (this) {
                    if (this.termDomain == null) {
                        final ImmutableLinkedHashSet<IVariable<?>> result =
                            this.createTermDomain();

                        return this.termDomain = result;
                    }
                }
            }
            return this.termDomain;
        } else {
            return this.createTermDomain();
        }
    }

    private ImmutableLinkedHashSet<IVariable<?>> createTermDomain() {
        final LinkedHashSet<IVariable<?>> dom =
            new LinkedHashSet<IVariable<?>>();

        for (final PolyVariable<?> var : this.sigma.getPolyDomain()) {
            if (!var.isMax()) {
                dom.add((IVariable<?>) var);
            }
        }

        final ImmutableLinkedHashSet<IVariable<?>> result = ImmutableCreator.create(dom);
        return result;
    }

    @Override
    public ImmutableSet<IVariable<?>> getTermVariablesInCodomain() {
        if (this.sigma instanceof Immutable) {
            if (this.termVariablesCodomain == null) {
                synchronized (this) {
                    if (this.termVariablesCodomain == null) {
                        final ImmutableLinkedHashSet<IVariable<?>> result =
                            this.createTermVariablesCodomain();

                        return this.termVariablesCodomain = result;
                    }
                }
            }
            return this.termVariablesCodomain;
        } else {
            return this.createTermVariablesCodomain();
        }
    }

    private ImmutableLinkedHashSet<IVariable<?>> createTermVariablesCodomain() {
        final LinkedHashSet<IVariable<?>> dom =
            new LinkedHashSet<IVariable<?>>();

        for (final PolyVariable<?> var : this.sigma.getPolyDomain()) {
            if (!var.isMax()) {
                for (final PolyVariable<?> coPolyVar : this.sigma.substitutePoly(var).getVariables()) {
                    if (!coPolyVar.isMax()) {
                        dom.add((IVariable<?>) coPolyVar);
                    }
                }
            }
        }

        final ImmutableLinkedHashSet<IVariable<?>> result = ImmutableCreator.create(dom);
        return result;
    }

    @Override
    public ImmutableSet<IFunctionSymbol<?>> getFunctionSymbolsInCodomain() {
        if (this.sigma instanceof Immutable) {
            if (this.functionSymbolsCodomain == null) {
                synchronized (this) {
                    if (this.functionSymbolsCodomain == null) {
                        final ImmutableLinkedHashSet<IFunctionSymbol<?>> result =
                            this.createFunctionSymbolsCodomain();

                        return this.functionSymbolsCodomain = result;
                    }
                }
            }
            return this.functionSymbolsCodomain;
        } else {
            return this.createFunctionSymbolsCodomain();
        }
    }

    private ImmutableLinkedHashSet<IFunctionSymbol<?>> createFunctionSymbolsCodomain() {
        final LinkedHashSet<IFunctionSymbol<?>> fs =
            new LinkedHashSet<IFunctionSymbol<?>>();

        for (final PolyVariable<?> var : this.sigma.getPolyDomain()) {
            if (!var.isMax()) {
                throw new UnsupportedOperationException("not clear what that means");
            }
        }

        final ImmutableLinkedHashSet<IFunctionSymbol<?>> result = ImmutableCreator.create(fs);

        return result;
    }

    @Override
    public boolean substitutesPoly(final PolyVariable<?> v) {
        return this.sigma.substitutesPoly(v);
    }

    @Override
    public boolean substitutesPoly(final Collection<? extends PolyVariable<?>> vs) {
        return this.sigma.substitutesPoly(vs);
    }

    @Override
    public <C extends SemiRing<C>>Polynomial<C> substitutePoly(final PolyVariable<C> v) {
        return this.sigma.substitutePoly(v);
    }

    @Override
    public Set<? extends PolyVariable<?>> getPolyDomain() {
        return this.sigma.getPolyDomain();
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
    public O termCompose(final BasicTermSubstitution sigma) {
        return this.compose(TermToPolyTermSubstitution.create(sigma, this.predefinedMap, this.polyInterpretation));
    }

    @Override
    public O compose(final PolyTermSubstitution sigma) {
        final I newSigma = (I) this.sigma.polyCompose(sigma);
        if (newSigma != this.sigma) {
            return this.createNewInstance(newSigma, this.predefinedMap, this.polyInterpretation);
        } else {
            return (O) this;
        }
    }

    @Override
    public O polyCompose(final BasicPolySubstitution sigma) {
        final I newSigma = (I) this.sigma.polyCompose(sigma);
        if (newSigma != this.sigma) {
            return this.createNewInstance(newSigma, this.predefinedMap, this.polyInterpretation);
        } else {
            return (O) this;
        }
    }

    protected abstract O createNewInstance(final I newSigma,
        final IDPPredefinedMap predefinedMap,
        final PolyInterpretation<?> polyInterpretation);
    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        this.sigma.export(sb, eu, verbosityLevel);
    }

}
