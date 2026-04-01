package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class ISubstitution extends BasicTermSubstitution.BasicTermSubstitutionSkeleton<ITerm<?>> implements ImmutableTermSubstitution {

    /*
     * substitution with empty domain
     */
    public static final ISubstitution emptySubstitution() {
        return ISubstitution.create(ImmutableCreator.create(java.util.Collections.<IVariable<?>, ITerm<?>> emptyMap()));
    }

    /**
     * creates a substitution from a non-null map
     * @param map
     */
    public static ISubstitution create(final ImmutableMap<IVariable<?>, ? extends ITerm<?>> map) {
        return new ISubstitution(map, false);
    }

    /**
     * creates a substitution from a non-null map
     * @param map
     * @param cleanMap may only be true iff map.get(x) != x for all x
     */
    public static ISubstitution create(final ImmutableMap<IVariable<?>, ITerm<?>> map,
        final boolean cleanMap) {

        return new ISubstitution(map, cleanMap);
    }

    /**
     * creates a substitution [x / term]
     */
    public static ISubstitution create(final IVariable<?> x, final ITerm<?> term) {
        if (Globals.useAssertions) {
            assert x.getDomain().isSpecialization(term.getDomain()) : "bad domain";
        }

        final Map<IVariable<?>, ITerm<?>> map =
            java.util.Collections.<IVariable<?>, ITerm<?>> singletonMap(x, term);

        return new ISubstitution(ImmutableCreator.create(map), true);
    }

    public static ISubstitution create(final BasicTermSubstitution sigma) {
        final Map<IVariable<?>, ITerm<?>> map =
            new LinkedHashMap<IVariable<?>, ITerm<?>>();

        for (final IVariable<?> v : sigma.getTermDomain()) {
            map.put(v, sigma.substituteTerm(v));
        }

        return new ISubstitution(ImmutableCreator.create(map), true);
    }

    public static ISubstitution create(final BasicTermSubstitution sigma, final Collection<? extends IVariable<?>> domain) {
        final Map<IVariable<?>, ITerm<?>> map =
            new LinkedHashMap<IVariable<?>, ITerm<?>>();

        for (final IVariable<?> v : sigma.getTermDomain()) {
            if (domain.contains(v)) {
                map.put(v, sigma.substituteTerm(v));
            }
        }

        return new ISubstitution(ImmutableCreator.create(map), true);
    }


    protected ISubstitution(final ImmutableMap<IVariable<?>, ? extends ITerm<?>> map,
            final boolean cleanMap) {
        super(map, cleanMap);
        if (Globals.useAssertions) {
            for (final Map.Entry<IVariable<?>, ? extends ITerm<?>> entry : map.entrySet()) {
                assert entry.getKey().getRing().isSameRing(UnknownRing.INNSTANCE)
                || entry.getValue().getRing().isSameRing(UnknownRing.INNSTANCE)
                || entry.getKey().getRing().isSameRing(entry.getValue().getRing()) : "bad ring " + entry.getKey() + " / " + entry.getValue();
            }
        }
    }


    @Override
    public ImmutableTermSubstitution replaceAllFunctionSymbols(final FunctionSymbolReplacement sigma) {
        final ImmutableMap<IVariable<?>, ? extends ITerm<?>> map = this.getMap();
        boolean changed = false;

        final Map<IVariable<?>, ITerm<?>> newMap = new LinkedHashMap<IVariable<?>, ITerm<?>>();
        for (final Map.Entry<IVariable<?>, ? extends ITerm<?>> mapEntry : map.entrySet()) {
            final ITerm<?> newValue = mapEntry.getValue().replaceAllFunctionSymbols(sigma);
            newMap.put(mapEntry.getKey(), newValue);
            changed = !newValue.equals(mapEntry.getValue());
        }

        if (changed) {
            return ISubstitution.create(ImmutableCreator.create(newMap));
        } else {
            return this;
        }
    }

    /**
     * returns a new substitution by adding the given substitution to this
     * substitution, but only for those IVariable<?>s that have the identical
     * substitution in this substitution
     */
    public ISubstitution extend(final ISubstitution subExt) {
        final Map<IVariable<?>, ITerm<?>> newMap =
            new LinkedHashMap<IVariable<?>, ITerm<?>>(this.getMap());
        final ImmutableSet<IVariable<?>> domain = this.getTermDomain();
        for (final IVariable<?> v : subExt.getMap().keySet()) {
            if (!domain.contains(v)) {
                newMap.put(v, subExt.rawMap.get(v));
            }
        }
        return new ISubstitution(ImmutableCreator.create(newMap), true);
    }

    /**
     * returns the composition of this substitution with the given substitution.
     */
    @Override
    public ISubstitution termCompose(final BasicTermSubstitution sub) {
        if (sub.isEmpty()) {
            return this;
        }

        final ImmutableMap<IVariable<?>, ? extends ITerm<?>> myMap = this.getMap();
        final ImmutableMap<IVariable<?>, ITerm<?>> newMap = BasicTermSubstitutionSkeleton.termCompose(myMap, sub);

        if (newMap != null) {
            return ISubstitution.create(newMap);
        } else {
            return this;
        }
    }

    @Override
    public ImmutableTermSubstitution immutableTermCompose(final BasicTermSubstitution sigma) {
        return this.termCompose(sigma);
    }

    /**
     * self-speaking method; no side-effects on the Argument-Set should occur !
     * @author Martin Pluecker, copied from Sebastian Weise
     */
    public ISubstitution restrictTo(final Set<IVariable<?>> toRestrictTo) {
        final Map<IVariable<?>, ITerm<?>> newMap =
            new LinkedHashMap<IVariable<?>, ITerm<?>>();

        for (final Map.Entry<IVariable<?>, ? extends ITerm<?>> entry : this.rawMap.entrySet()) {
            if (toRestrictTo.contains(entry.getKey())) {
                newMap.put(entry.getKey(), entry.getValue());
            }
        }
        return ISubstitution.create(ImmutableCreator.create(newMap));
    }

    /**
     * Remove the mapping for the given IVariable.
     * @param var a IVariable.
     * @return a substitution where var is removed from the domain
     */
    public ISubstitution remove(final IVariable<?> var) {
        final Set<IVariable<?>> temp =
            new HashSet<IVariable<?>>(this.getTermDomain());
        temp.remove(var);
        return this.restrictTo(temp);
    }

    /**
     * restricts a Substitution to its Domain
     * @author Martin Pluecker, copied from Sebastian Weise
     */
    public ISubstitution getAsCleanSubstitution() {
        final Map<IVariable<?>, ITerm<?>> newMap =
            new LinkedHashMap<IVariable<?>, ITerm<?>>();

        for (final IVariable<?> actVar : this.getTermDomain()) {
            final ITerm<?> actValue = this.substitute(actVar);

            if (actValue != null && !actVar.equals(actValue)) {
                newMap.put(actVar, actValue);
            }
        }

        return ISubstitution.create(ImmutableCreator.create(newMap), true);
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        return null;
    }

}
