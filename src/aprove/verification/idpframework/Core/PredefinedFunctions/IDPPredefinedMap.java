package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.math.*;
import java.util.*;
import java.util.concurrent.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class IDPPredefinedMap implements Exportable, NameProvider {

    /**
     * @param t The term to convert.
     * @param predefinedMap The predefined semantics that should be applied.
     * @return A converted ITerm<?> having the given semantics.
     */
    public static ITerm<?> toITerm(final TRSTerm t,
        final IDPPredefinedMap predefinedMap) {

        if (t.isVariable()) {
            return ITerm.createVariable(((TRSVariable) t).getName(),
                DomainFactory.UNKNOWN);
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication) t;
            final FunctionSymbol oldRoot = fa.getRootSymbol();
            final IFunctionSymbol<?> newRoot =
                IFunctionSymbol.create(oldRoot.getName(), oldRoot.getArity(),
                    predefinedMap);
            final ArrayList<ITerm<?>> newArgs =
                new ArrayList<ITerm<?>>(newRoot.getArity());
            for (final TRSTerm arg : fa.getArguments()) {
                newArgs.add(IDPPredefinedMap.toITerm(arg, predefinedMap));
            }
            return ITerm.createFunctionApplication(newRoot, newArgs);
        }
    }

    public static Map<Integer, Collection<String>> getUsedFunctionSymbols(final Collection<? extends ITerm<?>> terms) {
        final CollectionMap<Integer, String> result = new CollectionMap<Integer, String>();

        for (final ITerm<?> t : terms) {
            final Set<IFunctionSymbol<?>> fss = t.getFunctionSymbols();
            for (final IFunctionSymbol<?> fs : fss) {
                result.add(fs.getArity(), fs.getName());
            }
        }

        return result;
    }

    public static Map<Integer, Collection<String>> getUsedFunctionSymbolsFromOldTerms(final Collection<? extends TRSTerm> terms) {
        final CollectionMap<Integer, String> result = new CollectionMap<Integer, String>();

        for (final TRSTerm t : terms) {
            final Set<FunctionSymbol> fss = t.getFunctionSymbols();
            for (final FunctionSymbol fs : fss) {
                result.add(fs.getArity(), fs.getName());
            }
        }

        return result;
    }

    public static boolean isBooleanTrue(final ITerm<?> term) {
        return PredefinedSemanticsFactory.BOOLEAN_TERM_TRUE.equals(term);
    }

    public static boolean isBooleanFalse(final ITerm<?> term) {
        return PredefinedSemanticsFactory.BOOLEAN_TERM_FALSE.equals(term);
    }

    public static final IDPPredefinedMap EMPTY_MAP =
        new IDPPredefinedMap(
            ImmutableCreator.create(Collections.<ImmutablePair<String, Integer>, PredefinedFunction<?, ?>> emptyMap()),
            Collections.<Integer, Collection<String>> emptyMap());

    public static final IDPPredefinedMap DEFAULT_MAP;
    static {
        final Set<SemiRingDomain<?>> defaultDomains =
            Collection_Util.<SemiRingDomain<?>>createConcurrentHashSet();
        defaultDomains.add(DomainFactory.INTEGERS);
        defaultDomains.add(DomainFactory.BOOLEANS);
        DEFAULT_MAP =
            new IDPPredefinedMap(
                ImmutableCreator.create(Collections.<ImmutablePair<String, Integer>, PredefinedFunction<?, ?>> emptyMap()),
                defaultDomains, Collections.<Integer, Collection<String>> emptyMap());
    }

    protected final Map<ImmutablePair<String, Integer>, PredefinedConstructor<?>> constructors;

    protected final ImmutableMap<ImmutablePair<String, Integer>, PredefinedFunction<?, ?>> mapping;
    protected final Set<SemiRingDomain<?>> usedDomains;
    protected final ImmutableMap<ImmutablePair<Func, List<? extends SemiRingDomain<?>>>, ImmutablePair<String, Integer>> reverseMapping;
    protected final Set<String> fsNames;

    public IDPPredefinedMap(
            final ImmutableMap<ImmutablePair<String, Integer>, PredefinedFunction<?, ?>> mapping,
            final Map<Integer, ? extends Collection<String>> usedFunctionSymboldNames) {
        this(mapping, Collection_Util.<SemiRingDomain<?>>createConcurrentHashSet(), usedFunctionSymboldNames);
    }

    protected IDPPredefinedMap(
            final ImmutableMap<ImmutablePair<String, Integer>, PredefinedFunction<?, ?>> mapping,
            final Set<SemiRingDomain<?>> usedDomains,
            final Map<Integer, ? extends Collection<String>> usedFunctionSymboldNames) {
        this.constructors =
            new ConcurrentHashMap<ImmutablePair<String, Integer>, PredefinedConstructor<?>>();
        final Map<ImmutablePair<String, Integer>, PredefinedFunction<?, ?>> completedMapping =
            new ConcurrentHashMap<ImmutablePair<String, Integer>, PredefinedFunction<?, ?>>(
                mapping);
        final Map<ImmutablePair<Func, List<? extends SemiRingDomain<?>>>, ImmutablePair<String, Integer>> reverse =
            new ConcurrentHashMap<ImmutablePair<Func, List<? extends SemiRingDomain<?>>>, ImmutablePair<String, Integer>>();

        this.usedDomains = usedDomains;
        this.fsNames = Collection_Util.<String>createConcurrentHashSet();
        // reverse mapping and collect used domains
        for (final Map.Entry<ImmutablePair<String, Integer>, PredefinedFunction<?, ?>> entry : completedMapping.entrySet()) {
            final ImmutablePair<Func, List<? extends SemiRingDomain<?>>> key =
                new ImmutablePair<Func, List<? extends SemiRingDomain<?>>>(
                    entry.getValue().getFunc(), entry.getValue().getDomains());
            if (reverse.containsKey(key)) {
                throw new IllegalArgumentException(
                    "dupplicate predefined semantics: " + entry.getKey()
                        + " and " + reverse.get(key));
            }
            reverse.put(key, entry.getKey());
            this.fsNames.add(entry.getKey().x);
            usedDomains.addAll(entry.getValue().getDomains());
            usedDomains.add(entry.getValue().getResultDomain());
        }

        // complete mapping
        final Map<Integer, FreshNameGenerator> freshNames = new HashMap<Integer, FreshNameGenerator>();
        for (final Map.Entry<Integer, ? extends Collection<String>> usedFunctionSymbols : usedFunctionSymboldNames.entrySet()) {
            freshNames.put(usedFunctionSymbols.getKey(), new FreshNameGenerator(usedFunctionSymbols.getValue(),
                FreshNameGenerator.APPEND_NUMBERS));
        }

        final Collection<PredefinedFunction<?, ?>> allFunctions =
            PredefinedSemanticsFactory.getAllFunctions(usedDomains);

        for (final PredefinedFunction<?, ?> func : allFunctions) {
            final ImmutablePair<Func, List<? extends SemiRingDomain<?>>> key =
                new ImmutablePair<Func, List<? extends SemiRingDomain<?>>>(func.getFunc(),
                    func.getDomains());
            if (!reverse.containsKey(key)) {
                final StringBuilder name = new StringBuilder();
                name.append(func.getFunc().getName());
                final ImmutableList<? extends SemiRingDomain<?>> doms = func.getDomains();
                boolean allIntegerDomains = true;
                boolean allBooleanDomains = true;
                for (final SemiRingDomain<?> dom : doms) {
                    if (dom.isBooleanDomain()) {
                        allIntegerDomains = false;
                    } else if (dom.isSemiRingDomain()) {
                        allBooleanDomains = false;
                        if (!DomainFactory.INTEGERS.equals(dom)) {
                            allIntegerDomains = false;
                            break;
                        }
                    }
                }
                if (!allIntegerDomains && !allBooleanDomains) {
                    for (final SemiRingDomain<?> dom : doms) {
                        name.append(DomainFactory.SUFFIX_SEPERATOR);
                        name.append(dom.getSuffix());
                    }
                }

                FreshNameGenerator freshNameGenerator = freshNames.get(func.getArity());
                if (freshNameGenerator == null) {
                    freshNameGenerator = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
                    freshNames.put(func.getArity(), freshNameGenerator);
                }

                final ImmutablePair<String, Integer> fs =
                    new ImmutablePair<String, Integer>(freshNameGenerator.getFreshName(
                        name.toString(), false), func.getArity());
                this.fsNames.add(fs.x);
                reverse.put(new ImmutablePair<Func, List<? extends SemiRingDomain<?>>>(
                    func.getFunc(), doms), fs);
                completedMapping.put(fs, func);
            }
        }

        this.reverseMapping = ImmutableCreator.create(reverse);
        this.mapping = ImmutableCreator.create(completedMapping);
    }

    @Override
    public boolean contains(final String name) {
        if (this.fsNames.contains(name)) {
            return true;
        }
        if (this.usedDomains.contains(DomainFactory.BOOLEANS)) {
            if (PredefinedSemanticsFactory.BOOLEAN_FS_FALSE.getName().equals(
                name)
                || PredefinedSemanticsFactory.BOOLEAN_FS_TRUE.getName().equals(
                    name)) {
                return true;
            }
        }
        if (name.matches("-?\\d+")) {
            final BigInt value = BigInt.create(new BigInteger(name));
            for (final SemiRingDomain<?> dom : this.usedDomains) {
                if (dom.isSemiRingDomain()) {
                    final SemiRingDomain<?> ringDom = dom;
                    if (ringDom.inRange(value)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    public <R extends IntRing<R>> PfInt<R> createInt(final R value,
        final IntegerDomain<R> domain) {

        if (this.usedDomains.contains(domain)) {
            return PredefinedSemanticsFactory.createInt(value, domain);
        } else {
            throw new IllegalArgumentException("domain not used: " + domain);
        }
    }

    public <R extends IntRing<R>> IFunctionApplication<R> createIntIntTerm(final R value,
        final IntegerDomain<R> domain) {
        if (this.usedDomains.contains(domain)) {
            return PredefinedSemanticsFactory.createInt(value, domain).getTerm();
        } else {
            throw new IllegalArgumentException("domain not used: " + domain);
        }
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final IDPPredefinedMap other = (IDPPredefinedMap) obj;
        if (this.mapping == null) {
            if (other.mapping != null) {
                return false;
            }
        } else if (!this.mapping.equals(other.mapping)) {
            return false;
        }
        return true;
    }

    public String export(final Collection<ImmutablePair<String, Integer>> usedSymbols,
        final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        sb.append("The following domains are used:");
        sb.append(o.cond_linebreak());
        sb.append(o.set(this.usedDomains, Export_Util.NICE_SET));
        sb.append(o.cond_linebreak());
        sb.append(o.tableStart(3));
        for (final Map.Entry<ImmutablePair<String, Integer>, PredefinedFunction<?, ?>> entry : this.mapping.entrySet()) {
            if (usedSymbols == null || usedSymbols.contains(entry.getKey())) {
                final ArrayList<String> row = new ArrayList<String>(4);
                row.add(IFunctionSymbol.create(entry.getKey().x,
                    entry.getKey().y, this).export(o));
                row.add("~");
                row.add(entry.getValue().export(o));
                sb.append(o.tableRow(row));
            }
        }
        sb.append(o.tableEnd());
        return sb.toString();
    }

    @Override
    public final String export(final Export_Util o) {
        return this.export(null, o);
    }

    public PfBoolean getBoolean(final boolean value) {
        if (this.usedDomains.contains(DomainFactory.BOOLEANS)) {
            return value ? PredefinedSemanticsFactory.BOOLEAN_TRUE
                : PredefinedSemanticsFactory.BOOLEAN_FALSE;
        } else {
            throw new IllegalArgumentException("Boolean domain not used");
        }
    }

    public PfBoolean getBooleanFalse() {
        if (this.usedDomains.contains(DomainFactory.BOOLEANS)) {
            return PredefinedSemanticsFactory.BOOLEAN_FALSE;
        } else {
            throw new IllegalArgumentException("Boolean domain not used");
        }
    }

    public PfBoolean getBooleanTrue() {
        if (this.usedDomains.contains(DomainFactory.BOOLEANS)) {
            return PredefinedSemanticsFactory.BOOLEAN_TRUE;
        } else {
            throw new IllegalArgumentException("Boolean domain not used");
        }
    }

    public <R extends IntRing<R>> IFunctionSymbol<R> getIntSym(final R value,
        final IntegerDomain<R> domain) {
        if (this.usedDomains.contains(domain)) {
            return PredefinedSemanticsFactory.createIntSym(value, domain);
        } else {
            throw new IllegalArgumentException("domain not used: " + domain);
        }
    }

    public ImmutableMap<ImmutablePair<String, Integer>, PredefinedFunction<?, ?>> getMapping() {
        return this.mapping;
    }

    public PredefinedFunction<?, ?> getPredefinedFunction(final ImmutablePair<String, Integer> fs) {
        return this.mapping.get(fs);
    }

    public ImmutableCollection<ImmutablePair<String, Integer>> getPredefinedFunctionSymbols() {
        return ImmutableCreator.create(this.mapping.keySet());
    }

    public PredefinedSemantics<?> getPredefinedSemantics(final ImmutablePair<String, Integer> fs) {
        final PredefinedSemantics<?> func = this.mapping.get(fs);
        if (func == null) {
            synchronized (this.constructors) {
                PredefinedConstructor<?> sem =
                    this.constructors.get(fs);
                if (sem != null) {
                    return sem;
                }
                for (final SemiRingDomain<?> dom : this.usedDomains) {
                    sem =
                        PredefinedSemanticsFactory.getConstructor(dom, fs.x,
                            fs.y);
                    if (sem != null) {
                        this.constructors.put(fs, sem);
                        return sem;
                    }
                }
            }
        } else {
            return func;
        }
        return null;
    }

    public ITerm<?> toITerm(final TRSTerm t) {
        return IDPPredefinedMap.toITerm(t, this);
    }

    public <D extends SemiRing<D>> ImmutablePair<String, Integer> getSym(final Func func,
        final D domain) {
        final ArrayList<D> domains = new ArrayList<D>(func.getArity());
        for (int i = func.getArity(); i > 0; i--) {
            domains.add(domain);
        }
        return this.reverseMapping.get(new ImmutablePair<Func, List<D>>(func,
            domains));
    }

    public ImmutablePair<String, Integer> getSym(final Func func,
        final SemiRingDomain<?>... domains) {
        return this.reverseMapping.get(new ImmutablePair<Func, List<? extends SemiRingDomain<?>>>(
            func, Arrays.asList(domains)));
    }

    public <D extends SemiRing<D>> ImmutablePair<String, Integer> getSym(final Func func,
        final List<D> dom) {
        return this.reverseMapping.get(new ImmutablePair<Func, List<D>>(func, dom));
    }

    public IFunctionSymbol<?> getFunctionSymbol(final Func func,
        final List<? extends SemiRingDomain<?>> dom) {
        final ImmutablePair<String, Integer> p =
            this.reverseMapping.get(new ImmutablePair<Func, List<? extends SemiRingDomain<?>>>(func, dom));
        return IFunctionSymbol.create(p.x, this.getPredefinedSemantics(p), this);
    }

    @SuppressWarnings("unchecked")
    public <D extends SemiRing<D>> IFunctionSymbol<D> getFunctionSymbolChecked(final Func func,
        final List<? extends SemiRingDomain<?>> dom) {
        final ImmutablePair<String, Integer> p =
            this.reverseMapping.get(new ImmutablePair<Func, List<? extends SemiRingDomain<?>>>(func, dom));
        return (IFunctionSymbol<D>) IFunctionSymbol.create(p.x, this.getPredefinedSemantics(p), this);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.mapping == null) ? 0 : this.mapping.hashCode());
        return result;
    }

    public boolean isPredefined(final ImmutablePair<String, Integer> fs) {
        return this.getPredefinedSemantics(fs) != null;
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

}
