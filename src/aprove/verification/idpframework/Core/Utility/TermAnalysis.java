/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.Utility;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * This class provides methods to analyze sets of rules. Generated once all
 * values are cached.
 * @author mpluecke
 */
public class TermAnalysis<T extends ITerm<?>> implements Immutable, Exportable,
IDPExportable, ITermAnalysis<T> {

    public static <T extends ITerm<?>> TermAnalysis<T> emptyAnalysis() {
        return new TermAnalysis<T>(
                ImmutableCreator.create(java.util.Collections.<T> emptySet()),
                IDPPredefinedMap.EMPTY_MAP);
    }

    protected static final ImmutableSet<IFunctionApplication<?>> EMPTY_FUNCTIONAPP_SET =
        ImmutableCreator.create(java.util.Collections.<IFunctionApplication<?>> emptySet());

    private final ImmutableSet<? extends T> terms;
    private final IDPPredefinedMap predefinedMap;
    private volatile ImmutableSet<IFunctionSymbol<?>> rootSymbols;
    private volatile ImmutableSet<IFunctionSymbol<?>> functionSymbols;
    private volatile ImmutableSet<IVariable<?>> variables;
    private volatile ImmutableSet<IFunctionSymbol<?>> predefinedFunctions;
    private volatile ImmutableSet<Domain> domains;
    private volatile ImmutableMap<IFunctionSymbol<?>, ImmutableSet<T>> termMap;

    /**
     * T set contains restricted integers. (computed by getDomains)
     */
    private boolean restricted;

    /**
     * T set contains unrestricted integers. (computed by getDomains)
     */
    private boolean unrestricted;

    /**
     * T set contains bitwise predefined functions. (computed by
     * getPredefinedFunctions)
     */
    private boolean bitwise;

    /**
     * T set contains predefined defined functions (as opposed to integer or
     * boolean constants as predefined symbols only) (computed by
     * getPredefinedFunctions)
     */
    private boolean predefinedDefSymbols;
    public TermAnalysis(final ImmutableSet<? extends T> terms,
        final IDPPredefinedMap predefinedMap) {
        this.terms = terms;
        this.predefinedMap = predefinedMap;
    }

    public TermAnalysis(final TermAnalysis<T> cloneFrom) {
        synchronized (cloneFrom) {
            this.predefinedMap = cloneFrom.predefinedMap;
            this.terms = cloneFrom.terms;
            this.rootSymbols = cloneFrom.rootSymbols;
            this.functionSymbols = cloneFrom.functionSymbols;
            this.variables = cloneFrom.variables;
            this.predefinedFunctions = cloneFrom.predefinedFunctions;
            this.domains = cloneFrom.domains;
            this.termMap = cloneFrom.termMap;
        }
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#getPredefinedMap()
     */
    @Override
    public IDPPredefinedMap getPredefinedMap() {
        return this.predefinedMap;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#getFunctionSymbols()
     */
    @Override
    public ImmutableSet<IFunctionSymbol<?>> getFunctionSymbols() {
        if (this.functionSymbols == null) {
            synchronized (this) {
                if (this.functionSymbols == null) {
                    final Set<IFunctionSymbol<?>> fs =
                        new LinkedHashSet<IFunctionSymbol<?>>();
                    for (final T term : this.terms) {
                        fs.addAll(term.getFunctionSymbols());
                    }
                    return this.functionSymbols = ImmutableCreator.create(fs);
                }
            }
        }
        return this.functionSymbols;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#getRootSymbols()
     */
    @Override
    public ImmutableSet<IFunctionSymbol<?>> getRootSymbols() {
        if (this.rootSymbols == null) {
            synchronized (this) {
                if (this.rootSymbols == null) {
                    final Set<IFunctionSymbol<?>> fs =
                        new LinkedHashSet<IFunctionSymbol<?>>();
                    for (final T term : this.terms) {
                        if (!term.isVariable()) {
                            fs.add(((IFunctionApplication<?>) term).getRootSymbol());
                        }
                    }
                    return this.rootSymbols = ImmutableCreator.create(fs);
                }
            }
        }
        return this.functionSymbols;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#getVariables()
     */
    @Override
    public ImmutableSet<IVariable<?>> getVariables() {
        if (this.variables == null) {
            synchronized (this) {
                if (this.variables == null) {
                    final Set<IVariable<?>> vars = new LinkedHashSet<IVariable<?>>();
                    for (final T term : this.terms) {
                        vars.addAll(term.getVariables());
                    }
                    return this.variables = ImmutableCreator.create(vars);
                }
            }
        }
        return this.variables;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#isConstructor(aprove.verification.idpframework.Core.BasicStructures.IFunctionSymbol<?>)
     */
    @Override
    public Boolean isConstructor(final IFunctionSymbol<?> fs) {
        final ImmutableSet<IFunctionSymbol<?>> defined = this.getRootSymbols();
        if (defined.contains(fs)) {
            return false;
        }
        return fs.getSemantics() == null
        || PredefinedUtil.getPredefinedConstructor(fs) != null;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#getTermMap()
     */
    @Override
    public ImmutableMap<IFunctionSymbol<?>, ImmutableSet<T>> getTermMap() {
        if (this.termMap == null) {
            synchronized (this) {
                if (this.termMap == null) {
                    final Map<IFunctionSymbol<?>, Set<T>> tmp =
                        TermAnalysis.generateTermMap(this.terms);
                    final Map<IFunctionSymbol<?>, ImmutableSet<T>> ruleMap =
                        new LinkedHashMap<IFunctionSymbol<?>, ImmutableSet<T>>();
                    for (final Map.Entry<IFunctionSymbol<?>, Set<T>> entry : tmp.entrySet()) {
                        ruleMap.put(entry.getKey(),
                            ImmutableCreator.create(entry.getValue()));
                    }
                    return this.termMap = ImmutableCreator.create(ruleMap);
                }
            }
        }
        return this.termMap;
    }

    public static <T extends ITerm<?>> Map<IFunctionSymbol<?>, Set<T>> generateTermMap(final Collection<? extends T> terms) {
        final Map<IFunctionSymbol<?>, Set<T>> res =
            new LinkedHashMap<IFunctionSymbol<?>, Set<T>>();
        for (final T term : terms) {
            if (!term.isVariable()) {
                final IFunctionSymbol<?> root =
                    ((IFunctionApplication<?>) term).getRootSymbol();
                Set<T> trms = res.get(root);
                if (trms == null) {
                    trms = new LinkedHashSet<T>();
                    res.put(root, trms);
                }
                trms.add(term);
            }
        }
        return res;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#getTerms()
     */
    @Override
    public ImmutableSet<? extends T> getTerms() {
        return this.terms;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#getDomains()
     */
    @Override
    public ImmutableSet<Domain> getDomains() {
        if (this.domains == null) {
            synchronized (this) {
                if (this.domains == null) {
                    final Set<IFunctionSymbol<?>> predefined =
                        this.getPredefinedFunctions();
                    final Set<Domain> d = new LinkedHashSet<Domain>();
                    for (final IFunctionSymbol<?> fs : predefined) {
                        final PredefinedSemantics<?> sem = fs.getSemantics();
                        if (!sem.isConstructor()) {
                            final PredefinedFunction<?, ?> func =
                                (PredefinedFunction<?, ?>) sem;
                            d.addAll(func.getDomains());
                            d.add(func.getResultDomain());
                        }
                    }
                    final Domain z = DomainFactory.INTEGERS;
                    this.unrestricted = d.contains(z);
                    this.restricted = false;
                    for (final Domain dom : d) {
                        if (dom instanceof IntegerDomain) {
                            if (((IntegerDomain<?>) dom).getBits() != 0) {
                                this.restricted = true;
                                break;
                            }
                        }
                    }
                    return this.domains = ImmutableCreator.create(d);
                }
            }
        }
        return this.domains;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#getPredefinedFunctions()
     */
    @Override
    public ImmutableSet<IFunctionSymbol<?>> getPredefinedFunctions() {
        if (this.predefinedFunctions == null) {
            synchronized (this) {
                if (this.predefinedFunctions == null) {
                    final ImmutableSet<IFunctionSymbol<?>> symbols =
                        this.getFunctionSymbols();
                    final Set<IFunctionSymbol<?>> funcs =
                        new LinkedHashSet<IFunctionSymbol<?>>();

                    boolean bw = false;
                    boolean predefDefSym = false;

                    for (final IFunctionSymbol<?> sym : symbols) {
                        final PredefinedSemantics<?> sem = sym.getSemantics();
                        if (sem != null) {
                            funcs.add(sym);
                            if (!sem.isConstructor()) {
                                predefDefSym = true;
                                bw |= ((PredefinedFunction<?, ?>) sem).isBitwise();
                            }
                        }
                    }

                    this.bitwise = bw;
                    this.predefinedDefSymbols = predefDefSym;

                    return this.predefinedFunctions =
                        ImmutableCreator.create(funcs);
                }
            }
        }
        return this.predefinedFunctions;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#hasUnrestrictedInt()
     */
    @Override
    public boolean hasUnrestrictedInt() {
        // this.unrestricted is calculated on first getDomains() invocation
        if (this.domains == null) {
            this.getDomains();
        }
        return this.unrestricted;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#hasRestrictedInt()
     */
    @Override
    public boolean hasRestrictedInt() {
        // this.restricted is calculated on first getDomains() invocation
        if (this.domains == null) {
            this.getDomains();
        }
        return this.restricted;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#hasBitwiseOps()
     */
    @Override
    public boolean hasBitwiseOps() {
        if (this.predefinedFunctions == null) {
            this.getPredefinedFunctions();
        }
        return this.bitwise;
    }

    /* (non-Javadoc)
     * @see aprove.verification.idpframework.Core.Utility.ITermAnalysis#hasPredefinedDefSymbols()
     */
    @Override
    public boolean hasPredefinedDefSymbols() {
        if (this.predefinedFunctions == null) {
            this.getPredefinedFunctions();
        }
        return this.predefinedDefSymbols;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime * result
            + ((this.predefinedMap == null) ? 0 : this.predefinedMap.hashCode());
        result = prime * result + ((this.terms == null) ? 0 : this.terms.hashCode());
        return result;
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
        final TermAnalysis<?> other = (TermAnalysis<?>) obj;
        if (this.predefinedMap == null) {
            if (other.predefinedMap != null) {
                return false;
            }
        } else if (!this.predefinedMap.equals(other.predefinedMap)) {
            return false;
        }
        if (this.terms == null) {
            if (other.terms != null) {
                return false;
            }
        } else if (!this.terms.equals(other.terms)) {
            return false;
        }
        return true;
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public final String export(final Export_Util o) {
        return this.export(o, IDPExportable.DEFAULT_LEVEL);
    }

    @Override
    public final String export(final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final StringBuilder sb = new StringBuilder();
        this.export(sb, o, verbosityLevel);
        return sb.toString();
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        sb.append(o.set(this.terms, Export_Util.NICE_SET));
    }

}
