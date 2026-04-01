/*
 * < Created on 11.04.2005
 */
package aprove.verification.idpframework.Core.BasicStructures;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * A IFunctionSymbol<?> is a String (the name) together with an arity (a natural
 * number) and possibly pre-defined semantics (may be null). Two
 * IFunctionSymbol<?>s are equal iff they have equal, equal arities and equal
 * semantics Note that the pre-defined semantics of a function symbol must match
 * the semantics given in the corresponding IDPPredefinedMap. There are no
 * assertions so the user has to care for himself!
 * @author Martin Pluecker, copied from thiemann
 */
public final class IFunctionSymbol<R extends SemiRing<R>> implements Immutable, Exportable, XmlExportable,
        Comparable<IFunctionSymbol<?>>, HasName {

    public static final ImmutableSet<IFunctionSymbol<?>> EMPTY_SET =
        ImmutableCreator.create(Collections.<IFunctionSymbol<?>>emptySet());

    /*
     * real values
     */
    private final String name;
    private final int arity;
    private final PredefinedSemantics<R> semantics;
    private final int hashCode;
    private final ImmutableList<? extends SemiRingDomain<?>> domains;
    private final SemiRingDomain<R> resultDomain;

    /*
     * cached / computed values
     */

    /**
     * Use this constructor to create a function symbol with pre-defined
     * semantics
     * @param name non null string
     * @param semantics
     */
    private IFunctionSymbol(final String name, final PredefinedSemantics<R> semantics) {
        if (Globals.useAssertions) {
            assert (name != null);
        }
        this.name = name;
        this.arity = semantics.getArity();
        this.semantics = semantics;
        this.domains = semantics.getDomains();
        this.resultDomain = semantics.getResultDomain();
        this.hashCode = (this.arity << 24) + 49031901 * name.hashCode();
    }

    /**
     * the constructor takes a non-null String as name and a natural number as
     * arity.
     * @param name
     * @param arity
     */
    private IFunctionSymbol(final String name, final ImmutableList<? extends SemiRingDomain<?>> inputDomains,
            final SemiRingDomain<R> resultDomain) {
        if (Globals.useAssertions) {
            assert (name != null);
        }
        this.name = name;
        this.arity = inputDomains.size();
        this.semantics = null;
        this.domains = inputDomains;
        this.resultDomain = resultDomain;
        /*
        boolean doExport = false;
        for (final Domain domain : domains) {
            if (!domain.equals(DomainFactory.UNKNOWN)) {
                doExport = true;
                break;
            }
        }
        doExport = doExport | resultDomain.equals(DomainFactory.UNKNOWN);
         */
        this.hashCode =
            (this.arity << 24) + 49031901 * name.hashCode() + inputDomains.hashCode() * 11 * 13
                + resultDomain.hashCode() * 11;
    }

    /**
     * creates a function symbol for a non-null String as name and a natural
     * number as arity.
     */
    @SuppressWarnings("unchecked")
    public static <R extends SemiRing<R>> IFunctionSymbol<R> createChecked(final String name,
        final int arity,
        final IDPPredefinedMap predefinedMap) {
        return (IFunctionSymbol<R>) IFunctionSymbol.create(name, arity, predefinedMap);
    }

    /**
     * creates a function symbol for a non-null String as name and a natural
     * number as arity.
     */
    public static IFunctionSymbol<?> create(final String name, final int arity, final IDPPredefinedMap predefinedMap) {
        final PredefinedSemantics<?> semantics =
            predefinedMap.getPredefinedSemantics(new ImmutablePair<String, Integer>(name, arity));
        if (semantics != null) {
            return IFunctionSymbol.create(name, semantics, predefinedMap);
        } else {
            final ArrayList<SemiRingDomain<UnknownRing>> domains = new ArrayList<SemiRingDomain<UnknownRing>>(arity);
            for (int i = arity; i > 0; i--) {
                domains.add(DomainFactory.UNKNOWN);
            }
            return new IFunctionSymbol<UnknownRing>(name, ImmutableCreator.create(domains), DomainFactory.UNKNOWN);
        }
    }

    /**
     * creates a function symbol for a non-null String as name and a natural
     * number as arity.
     */
    public static <R extends SemiRing<R>> IFunctionSymbol<R> create(final String name,
        final ImmutableList<? extends SemiRingDomain<?>> inputDomains,
        final SemiRingDomain<R> resultDomain,
        final IDPPredefinedMap predefinedMap) {
        final PredefinedSemantics<?> semantics =
            predefinedMap.getPredefinedSemantics(new ImmutablePair<String, Integer>(name, inputDomains.size()));

        if (Globals.useAssertions) {
            for (final Domain dom : inputDomains) {
                assert dom != null;
            }
            assert resultDomain != null;
        }

        if (semantics != null) {
            if (Globals.useAssertions) {
                assert semantics.getDomains().equals(inputDomains);
                assert semantics.getResultDomain().equals(resultDomain);
            }

            @SuppressWarnings("unchecked")
            final PredefinedSemantics<R> typedSemantics = (PredefinedSemantics<R>) semantics;
            return new IFunctionSymbol<R>(name, typedSemantics);
        } else {
            return new IFunctionSymbol<R>(name, inputDomains, resultDomain);
        }
    }

    public static <D extends SemiRing<D>> IFunctionSymbol<D> create(final String name,
        final PredefinedSemantics<D> semantics,
        final IDPPredefinedMap predefinedMap) {
        if (Globals.useAssertions) {
            final PredefinedSemantics<?> predefinedSemantics =
                predefinedMap.getPredefinedSemantics(new ImmutablePair<>(name, semantics.getArity()));
            assert (semantics.equals(predefinedSemantics)) : "name/semantics clash: " + name + " " + semantics;
        }
        return new IFunctionSymbol<>(name, semantics);
    }

    /**
     * Only for use with predefined constructors
     * @param name
     * @param semantics
     * @return
     */
    public static <D extends SemiRing<D>> IFunctionSymbol<D> create(final String name,
        final PredefinedSemantics<D> semantics) {
        if (Globals.useAssertions) {
            assert semantics.isConstructor() && name.equals(((PredefinedConstructor<?>) semantics).getName()) : "name clash "
                + name + " <> " + ((PredefinedConstructor<?>) semantics).getName();
        }
        return new IFunctionSymbol<D>(name, semantics);
    }

    public static <D extends SemiRing<D>> IFunctionSymbol<D> changeName(final IFunctionSymbol<D> fs,
        final IDPPredefinedMap predefinedMap,
        final String newName) {
        if (fs.getSemantics() == null) {
            return IFunctionSymbol.create(newName, fs.getDomains(), fs.getResultDomain(), predefinedMap);
        } else {
            return IFunctionSymbol.create(newName, fs.getSemantics(), predefinedMap);
        }
    }

    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other == null) {
            return false;
        }
        if (other instanceof IFunctionSymbol<?>) {
            final IFunctionSymbol<?> f = (IFunctionSymbol<?>) other;
            return f.hashCode == this.hashCode
                && f.name.equals(this.name)
                && f.arity == this.arity
                && ((f.semantics == null && this.semantics == null && this.domains.equals(f.domains) && this.resultDomain.equals(f.resultDomain)) || (f.semantics != null && f.semantics.equals(this.semantics)));
        }
        return false;
    }

    /**
     * returns the arity of this IFunctionSymbol<?>;
     * @return
     */
    public int getArity() {
        return this.arity;
    }

    /**
     * returns the name of this Symbol
     * @return
     */
    @Override
    public String getName() {
        return this.name;
    }

    /**
     * returns the pre-defined semantics of this symbol
     * @return may be null
     */
    public PredefinedSemantics<R> getSemantics() {
        return this.semantics;
    }

    public boolean isPredefined() {
        return this.semantics != null;
    }

    public boolean isPredefinedFunction() {
        return this.semantics != null && !this.semantics.isConstructor();
    }

    public boolean isPredefinedConstructor() {
        return this.semantics != null && this.semantics.isConstructor();
    }

    public ImmutableList<? extends SemiRingDomain<?>> getDomains() {
        return this.domains;
    }

    public SemiRingDomain<R> getResultDomain() {
        return this.resultDomain;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public String export(final Export_Util eu) {
        return this.export(eu, false);
    }

    public String export(final Export_Util eu, final boolean exportDomains) {
        String actualString = this.name;

        String[] splittedStr;

        final char head = 94;
        splittedStr = actualString.split("\\" + head, 2);
        if (splittedStr.length == 2) {
            final String fstStr = eu.escape(splittedStr[0]);
            final String sndStr = eu.escape(splittedStr[1]);
            actualString = fstStr + eu.sup(sndStr);
        } else {
            actualString = eu.escape(actualString);
        }
        if (exportDomains) {
            final StringBuilder sb = new StringBuilder();
            final Iterator<? extends Domain> domIter = this.domains.iterator();
            while (domIter.hasNext()) {
                final Domain domain = domIter.next();
                sb.append(domain.export(eu));
                sb.append(" ");
                sb.append(eu.rightarrow());
                sb.append(" ");
            }
            sb.append(this.resultDomain.export(eu));
            actualString += ": " + sb.toString();
        }
        return actualString;
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        final Map<String, String> m = new HashMap<String, String>();
        m.put("name", this.name);
        m.put("arity", Integer.toString(this.arity));
        if (this.isPredefined()) {
            m.put("predef", "true");
        }
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        final XmlContentsMap contents = new XmlContentsMap();
        final Iterator<? extends Domain> domIter = this.domains.iterator();
        while (domIter.hasNext()) {
            contents.add(domIter.next());
        }
        contents.add(this.resultDomain);
        return contents;
    }

    @Override
    public final String toString() {
        return this.name + (this.arity == 0 ? "" : "_" + this.arity);
    }

    @Override
    public int compareTo(final IFunctionSymbol<?> f) {
        final int comp = this.name.compareTo(f.name);
        if (comp != 0) {
            return comp;
        }
        return this.arity == f.arity ? 0 : (this.arity < f.arity ? -1 : 1);
    }

    public Set<IFunctionSymbol<?>> getFunctionSymbols() {
        return java.util.Collections.<IFunctionSymbol<?>>singleton(this);
    }

}
