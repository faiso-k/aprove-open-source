package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import immutables.*;

/**
 * @author MP
 */
public class VarRenaming extends BasicTermSubstitution.BasicTermSubstitutionSkeleton<IVariable<?>> implements PolyTermSubstitution, Immutable, ImmutableTermSubstitution, ImmutablePolySubstitution {

    public static final VarRenaming EMPTY_RENAMING = VarRenaming.create(ImmutableCreator.create(Collections.<IVariable<?>, IVariable<?>> emptyMap()), true, null);

    /**
     * creates a substitution from a non-null map
     * @param polyInterpretation may be null, poly substitution is not possible then
     */
    public static VarRenaming create(final ImmutableMap<IVariable<?>, IVariable<?>> map,
        final boolean cleanMap,
        final PolyFactory polyFactory) {
        return new VarRenaming(map, cleanMap, polyFactory);
    }

    public static VarRenaming createTermOnly(final ImmutableMap<IVariable<?>, IVariable<?>> map,
        final boolean cleanMap) {
        return VarRenaming.create(map, cleanMap, null);
    }

    private final PolyFactory polyFactory;

    private volatile ImmutableSet<PolyVariable<?>> polyDomain;

    protected VarRenaming(
            final ImmutableMap<IVariable<?>, IVariable<?>> map,
            final boolean cleanMap, final PolyFactory polyFactory) {
        super(map, cleanMap);
        this.polyFactory = polyFactory;
    }

    @Override
    public <D extends SemiRing<D>> IVariable<D> substituteTerm(final IVariable<D> v) {
        @SuppressWarnings("unchecked")
        IVariable<D> result = (IVariable<D>) this.getMap().get(v);;
        if (result == null) {
            result = v;
        }
        return result;
    }

    @Override
    public boolean substitutesPoly(final PolyVariable<?> v) {
        return this.getMap().containsKey(v);
    }

    @Override
    public boolean substitutesPoly(final Collection<? extends PolyVariable<?>> vs) {
        return this.getMap().keySet().containsAll(vs);
    }

    @Override
    public <C extends SemiRing<C>> Polynomial<C> substitutePoly(final PolyVariable<C> v) {
        if (!v.isMax()) {
            if (this.polyFactory == null) {
                throw new UnsupportedOperationException("no polyFactory present");
            }

            final IVariable<C> realV = (IVariable<C>) v;
            final IVariable<C> substitutedTerm = this.substituteTerm(realV);

            if (substitutedTerm != null) {
                return this.polyFactory.create(substitutedTerm);
            }
        }
            return null;
    }

    @Override
    public Set<PolyVariable<?>> getPolyDomain() {
        if (this.polyDomain == null) {
            synchronized (this) {
                if (this.polyDomain == null) {
                    final LinkedHashSet<PolyVariable<?>> dom =
                        new LinkedHashSet<PolyVariable<?>>();

                    for (final IVariable<?> var : this.getMap().keySet()) {
                        dom.add(var);
                    }

                    this.polyDomain = ImmutableCreator.create(dom);
                }
            }
        }
        return this.polyDomain;
    }

    @Override
    public VarRenaming compose(final PolyTermSubstitution sigma) {
        return this.termCompose(sigma);
    }

    @Override
    public ImmutableTermSubstitution replaceAllFunctionSymbols(final FunctionSymbolReplacement sigma) {
        return this;
    }

    @Override
    public VarRenaming polyCompose(final BasicPolySubstitution sigma) {
        boolean changed = false;
        final Map<IVariable<?>, IVariable<?>> newMap =
            new LinkedHashMap<IVariable<?>, IVariable<?>>();

        final ImmutableMap<IVariable<?>, ? extends IVariable<?>> map = this.getMap();

        for (final Map.Entry<IVariable<?>, ? extends IVariable<?>> entry : map.entrySet()) {
            final IVariable<?> key = entry.getKey();
            final IVariable<?> value = entry.getValue();
            final Polynomial<?> substResult = sigma.substitutePoly(key);

            assert substResult.isRealVariable() : "variable substitutions may only contain variables in co-domain";

            final IVariable<?> substVar = substResult.getRealVariable();

            if (substVar.equals(value)) {
                changed = true;
            }

            if (!key.equals(substVar)) {
                newMap.put(key, substVar);
            }
        }

        for (final PolyVariable<?> key : sigma.getPolyDomain()) {
            if (key.isMax()) {
                throw new UnsupportedOperationException("no max variables allowed here");
            } else {
                final IVariable<?> realVar = (IVariable<?>) key;
                if (!map.containsKey(realVar)) {
                    changed = true;
                    final Polynomial<?> substResult = sigma.substitutePoly(realVar);
                    assert substResult.isRealVariable() : "variable substitutions may only contain variables in co-domain";

                    newMap.put(realVar, substResult.getRealVariable());
                }
            }
        }

        if (changed) {
            return VarRenaming.create(ImmutableCreator.create(newMap), true, this.polyFactory);
        } else {
            return null;
        }

    }

    @Override
    public VarRenaming termCompose(final BasicTermSubstitution sigma) {
        if (sigma.isEmpty()) {
            return this;
        }

        final ImmutableMap<IVariable<?>, ? extends IVariable<?>> myMap = this.getMap();
        final ImmutableMap<IVariable<?>, ITerm<?>> newMap = BasicTermSubstitutionSkeleton.termCompose(myMap, sigma);

        if (newMap != null) {
            final LinkedHashMap<IVariable<?>, IVariable<?>> newVarMap = new LinkedHashMap<IVariable<?>, IVariable<?>>();
            for (final Map.Entry<IVariable<?>, ITerm<?>> entry : newMap.entrySet()) {
                assert entry.getValue().isVariable() : "variable substitutions may only contain variables in co-domain";
                newVarMap.put(entry.getKey(), (IVariable<?>) entry.getValue());
            }

            return VarRenaming.create(ImmutableCreator.create(newVarMap), true, this.polyFactory);
        } else {
            return this;
        }
    }

    @Override
    public PolyTermSubstitution polyTermCompose(final BasicTermSubstitution sigma) {
        return this.termCompose(sigma);
    }

    @Override
    public ImmutableTermSubstitution immutableTermCompose(final BasicTermSubstitution sigma) {
        return this.termCompose(sigma);
    }

    @Override
    public ImmutablePolySubstitution immutablePolyCompose(final BasicPolySubstitution sigma) {
        return this.polyCompose(sigma);
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        return null;
    }
}
