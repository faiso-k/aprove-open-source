/*
 * Created on 12.04.2005
 */
package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * A substitution is a mapping from variables to terms.
 * @author thiemann
 */
public final class TRSSubstitution implements ImmutableSubstitution, XMLObligationExportable, CPFAdditional {

    /**
     * Substitution with empty domain.
     */
    public static final TRSSubstitution EMPTY_SUBSTITUTION =
        TRSSubstitution.create(ImmutableCreator.create(java.util.Collections.<TRSVariable, TRSTerm>emptyMap()));

    /*
     * real values
     */
    private final ImmutableMap<TRSVariable, ? extends TRSTerm> rawMap;

    /*
     * cached/computed values
     */
    private ImmutableMap<TRSVariable, ? extends TRSTerm> cachedMap;

    private ImmutableSet<TRSVariable> cachedVarsCodomain;

    /**
     * @author Sebastian Weise
     */
    private ImmutableSet<TRSVariable> cachedVars;

    /**
     * Creates a TRSSubstitution from a non-null map.
     * @param map Non-null map.
     * @param cleanMap True if map is known to not contain identity entries.
     */
    private TRSSubstitution(ImmutableMap<TRSVariable, ? extends TRSTerm> map, boolean cleanMap) {
        if (Globals.useAssertions) {
            assert (map != null);
            if (cleanMap) {
                for (final Map.Entry<TRSVariable, ? extends TRSTerm> entry : map
                        .entrySet()) {
                    assert (!entry.getKey().equals(entry.getValue()));
                }
            }
        }
        this.rawMap = map;
        if (cleanMap) {
            this.cachedMap = map;
        }
    }

    /**
     * creates a substitution from a non-null map
     *
     * @param map
     */
    public static TRSSubstitution create(ImmutableMap<TRSVariable, ? extends TRSTerm> map) {
        return new TRSSubstitution(map, false);
    }

    /**
     * creates a substitution from a non-null map
     *
     * @param map
     * @param cleanMap
     *            may only be true iff map.get(x) != x for all x
     */
    public static TRSSubstitution create(ImmutableMap<TRSVariable, ? extends TRSTerm> map, boolean cleanMap) {
        return new TRSSubstitution(map, cleanMap);
    }

    /**
     * creates the empty/identical substitution
     */
    public static TRSSubstitution create() {
        return TRSSubstitution.EMPTY_SUBSTITUTION;
    }

    /**
     * creates a substitution [x / term]
     */
    public static TRSSubstitution create(final TRSVariable x, final TRSTerm term) {
        if (x.equals(term)) {
            return TRSSubstitution.EMPTY_SUBSTITUTION;
        }
        final Map<TRSVariable, TRSTerm> map = java.util.Collections.singletonMap(x, term);
        return new TRSSubstitution(ImmutableCreator.create(map), true);
    }

    @Override
    public TRSTerm substitute(Variable v) {
        final TRSTerm subst = this.rawMap.get(v);
        if (subst == null) {
            return (TRSTerm)v;
        }
        return subst;
    }

    /**
     * @param sigma Some Substitution which only replaces TRSVariables by TRSTerms.
     * @return The specified Substitution as TRSSubstitution.
     */
    @SuppressWarnings("unchecked")
    public static TRSSubstitution create(ImmutableSubstitution sigma) {
        return new TRSSubstitution((ImmutableMap<TRSVariable, TRSTerm>)sigma.toMap(), false);
    }

    /**
     * returns the domain of this substitution
     */
    public ImmutableSet<TRSVariable> getDomain() {
        return ImmutableCreator.create(this.toMap().keySet());
    }

    /**
     * @author Sebastian Weise
     */
    public ImmutableSet<TRSTerm> getCodomain() {
        return ImmutableCreator.create(new LinkedHashSet<TRSTerm>(this.toMap().values()));
    }

    /**
     * @author Sebastian Weise
     */
    public ImmutableSet<TRSVariable> getVariables() {
        if (this.cachedVars == null) {
            final Set<TRSVariable> cachedVarsTemp = new LinkedHashSet<TRSVariable>(this.getDomain());
            cachedVarsTemp.addAll(this.getVariablesInCodomain());
            this.cachedVars = ImmutableCreator.create(cachedVarsTemp);
        }
        return this.cachedVars;
    }

    /**
     * returns the variables of the codomain(range) of this substitution
     */
    public ImmutableSet<TRSVariable> getVariablesInCodomain() {
        if (this.cachedVarsCodomain == null) {
            final Set<TRSVariable> varsCodomain = new LinkedHashSet<TRSVariable>();
            for (Map.Entry<TRSVariable, ? extends TRSTerm> entry : this.toMap().entrySet()) {
                varsCodomain.addAll(entry.getValue().getVariables());
            }
            this.cachedVarsCodomain = ImmutableCreator.create(varsCodomain);
        }
        return this.cachedVarsCodomain;
    }

    /**
     * returns a new substitution by adding the given substitution to this
     * substitution, but only for those variables that have the identical
     * substitution in this substitution
     */
    public TRSSubstitution extend(final TRSSubstitution subExt) {
        final Map<TRSVariable, TRSTerm> newMap = new LinkedHashMap<TRSVariable, TRSTerm>(this.toMap());
        final ImmutableSet<TRSVariable> domain = this.getDomain();
        for (TRSVariable v : subExt.toMap().keySet()) {
            if (!domain.contains(v)) {
                newMap.put(v, subExt.rawMap.get(v));
            }
        }
        return new TRSSubstitution(ImmutableCreator.create(newMap), true);
    }

    /**
     * returns the composition of this substitution with the given substitution.
     */
    public TRSSubstitution compose(final TRSSubstitution sub) {
        final ImmutableMap<TRSVariable, ? extends TRSTerm> map = this.toMap();
        final Map<TRSVariable, TRSTerm> newMap = new LinkedHashMap<TRSVariable, TRSTerm>(map);
        final Iterator<Map.Entry<TRSVariable, TRSTerm>> i = newMap.entrySet()
                .iterator();
        while (i.hasNext()) {
            final Map.Entry<TRSVariable, TRSTerm> entry = i.next();
            final TRSVariable key = entry.getKey();
            final TRSTerm value = entry.getValue();
            final TRSTerm substResult = value.applySubstitution(sub);
            if (key.equals(substResult)) {
                i.remove();
            } else {
                newMap.put(key, substResult);
            }
        }
        for (final Map.Entry<TRSVariable, ? extends TRSTerm> entry : sub.toMap()
                .entrySet()) {
            final TRSVariable x = entry.getKey();
            if (!map.containsKey(x)) {
                newMap.put(x, entry.getValue());
            }
        }
        return new TRSSubstitution(ImmutableCreator.create(newMap), true);
    }

    /**
     * no side-effects on the Argument-Set will occur
     *
     * @author Sebastian Weise
     */
    public TRSSubstitution restrictTo(final Set<TRSVariable> toRestrictTo) {
        final Map<TRSVariable, TRSTerm> newMap = new LinkedHashMap<TRSVariable, TRSTerm>();
        for (final Map.Entry<TRSVariable, ? extends TRSTerm> actEntry : this.toMap().entrySet()) {
            if (toRestrictTo.contains(actEntry.getKey())) {
                newMap.put(actEntry.getKey(), actEntry.getValue());
            }
        }
        return TRSSubstitution.create(ImmutableCreator.create(newMap));
    }

    /**
     * note: a Variable-Renaming has to be injective !
     *
     * @author Sebastian Weise
     */
    public boolean isVariableRenaming() {
        if (!(this.getDomain().size() == this.getCodomain().size())) {
            return false;
        }
        for (final TRSTerm actValue : this.getCodomain()) {
            if (!(actValue instanceof TRSVariable)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Checks whether <code>this</code> is an instance of <code>sigma</code>,
     * i.e. whether there exists a tau such that <code>this = sigma tau</code>.
     */
    public boolean isInstanceOf(final TRSSubstitution sigma) {
        final Set<TRSVariable> domain = new LinkedHashSet<TRSVariable>(this.getDomain());
        domain.addAll(sigma.getDomain());

        final TRSTerm t = TRSTerm.createFunctionApplication(
                FunctionSymbol.create("?", domain.size()),
                new ArrayList<TRSTerm>(domain));
        final TRSTerm t_this = t.applySubstitution(this);
        final TRSTerm t_sigma = t.applySubstitution(sigma);

        return (t_sigma.matches(t_this));
    }

    public boolean isEmpty() {
        return this.getDomain().isEmpty();
    }

    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof TRSSubstitution) {
            final TRSSubstitution sigma = (TRSSubstitution) other;
            return this.toMap().equals(sigma.toMap());
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.toMap().hashCode();
    }

    @Override
    public String export(final Export_Util eu) {
        final ImmutableMap<TRSVariable, ? extends TRSTerm> map = this.toMap();
        if (map.isEmpty()) {
            return "[ ]";
        }
        final StringBuilder retStr = new StringBuilder();
        retStr.append("[");
        for (final Map.Entry<TRSVariable, ? extends TRSTerm> entry : map.entrySet()) {
            retStr.append(entry.getKey().export(eu));
            retStr.append(" / ");
            retStr.append(entry.getValue().export(eu));
            retStr.append(", ");
        }
        retStr.setLength(retStr.length() - 2);
        retStr.append("]");
        return retStr.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.SUBSTITUTION.createElement(doc);
        for (final Map.Entry<TRSVariable, ? extends TRSTerm> entry : this.rawMap
                .entrySet()) {
            final Element subst = XMLTag.SUBSTITUTE.createElement(doc);
            subst.appendChild(entry.getKey().toDOM2(doc, xmlMetaData));
            subst.appendChild(entry.getValue().toDOM(doc, xmlMetaData));
            e.appendChild(subst);
        }
        return e;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element substitution = CPFTag.SUBSTITUTION.createElement(doc);
        for (final Map.Entry<TRSVariable, ? extends TRSTerm> entry : this.rawMap.entrySet()) {
            final Element substEntry = CPFTag.SUBST_ENTRY.createElement(doc);
            substEntry.appendChild(entry.getKey().toCPF2(doc, xmlMetaData));
            substEntry.appendChild(entry.getValue().toCPF(doc, xmlMetaData));
            substitution.appendChild(substEntry);
        }

        return substitution;
    }

    /**
     * Remove the mapping for the given variable.
     * @param var a variable.
     * @return a substitution where var is removed from the domain
     */
    public TRSSubstitution remove(final TRSVariable var) {
        final Set<TRSVariable> temp = new HashSet<TRSVariable>(this.getDomain());
        temp.remove(var);
        return this.restrictTo(temp);
    }

    @Override
    public ImmutableMap<TRSVariable, ? extends TRSTerm> toMap() {
        if (this.cachedMap == null) {
            final Map<TRSVariable, TRSTerm> map = new LinkedHashMap<TRSVariable, TRSTerm>();
            for (final Map.Entry<TRSVariable, ? extends TRSTerm> entry : this.rawMap
                    .entrySet()) {
                final TRSVariable key = entry.getKey();
                final TRSTerm value = entry.getValue();
                if (!key.equals(value)) {
                    map.put(key, value);
                }
            }
            this.cachedMap = ImmutableCreator.create(map);
        }
        return this.cachedMap;
    }

    /**
     * Checks whether the given Substitution that and this commutes.
     * @param that - the other substitution
     * @return true iff this and that commutes
     */
    public boolean commutes(TRSSubstitution that) {
        Set<TRSVariable> myVariables = new LinkedHashSet<TRSVariable>();
        myVariables.addAll(this.getDomain());
        myVariables.addAll(that.getDomain());
        
        for(TRSVariable var : myVariables) {
            if(!var.applySubstitution(this).applySubstitution(that).equals(var.applySubstitution(that).applySubstitution(this))) {
                return false;
            }
        }
        return true;
    }
}
