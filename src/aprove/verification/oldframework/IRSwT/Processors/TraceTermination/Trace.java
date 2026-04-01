package aprove.verification.oldframework.IRSwT.Processors.TraceTermination;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * A trace (system) consists of rules
 * l -> r
 * where every symbol occurring in l or r has arity 1.
 * Furthermore in l and r occurs exactly one defined symbol
 * of the top position.
 * Thus, we can write
 * l = f a_1 a_2 ... a_n x and
 * r = g b_1 b_2 ... b_k y.
 *
 * Such a rule is called non-swapping IFF x = y holds.
 *
 * @author Matthias Hoelzel
 *
 */
public class Trace {
    /** Set of trace rules. */
    private final ImmutableLinkedHashSet<IGeneralizedRule> rules;

    /**
     * Set of defined symbols.
     * For convenience, it also contains the top symbols of the right sides.
     */
    private final LinkedHashSet<FunctionSymbol> definedSymbols;

    /**
     * Set of constructor symbols, i.e. every other symbol, that is
     * a not contained in definedSybmols.
     */
    private final LinkedHashSet<FunctionSymbol> constructorSymbols;

    /** Same as definedSymbols, but here we store the strings. */
    private final ImmutableLinkedHashSet<String> setOfDefinedSymbols;

    /** Same as constructorSymbols, but here we store the strings. */
    private final ImmutableLinkedHashSet<String> setOfConstructorSymbols;

    /**
     * Constructor!
     * @param setOfRules a set of rules
     */
    public Trace(final ImmutableLinkedHashSet<IGeneralizedRule> setOfRules) {
        this.rules = setOfRules;
        this.definedSymbols = new LinkedHashSet<>();
        this.constructorSymbols = new LinkedHashSet<>();

        final boolean isTrace = this.checkSanity();
        this.setOfConstructorSymbols = this.convertSymbolSet(this.constructorSymbols);
        this.setOfDefinedSymbols = this.convertSymbolSet(this.definedSymbols);

        if (!isTrace) {
            throw new UnsupportedOperationException("Invalid \"trace\" system constructed!");
        }
    }

    /**
     * Constructor!
     * @param setOfRules a set of rules
     */
    public Trace(final LinkedHashSet<IGeneralizedRule> setOfRules) {
        this(ImmutableCreator.create(setOfRules));
    }

    /**
     * Validates whether this is really a trace.
     * @return boolean
     */
    private boolean checkSanity() {
        // 1. Collect defined symbols:
        for (final IGeneralizedRule rule : this.rules) {
            final FunctionSymbol leftRootSymbol = rule.getLeft().getRootSymbol();
            this.definedSymbols.add(leftRootSymbol);
            if (leftRootSymbol.getArity() != 1) {
                return false;
            }

            // For convenience we say that the root symbol of the right
            // is also a defined symbol. (We need them later!)
            if (!(rule.getRight() instanceof TRSFunctionApplication)) {
                return false;
            }
            final FunctionSymbol rightRootSymbol = ((TRSFunctionApplication) rule.getRight()).getRootSymbol();
            if (rightRootSymbol.getArity() != 1) {
                return false;
            }
            this.definedSymbols.add(rightRootSymbol);
        }

        // 2. Check structure of left and right sides:
        for (final IGeneralizedRule rule : this.rules) {
            if (!this.checkTerm(rule.getLeft()) || !this.checkTerm(rule.getRight())) {
                return false;
            }
        }
        return true;
    }

    private ImmutableLinkedHashSet<String> convertSymbolSet(final LinkedHashSet<FunctionSymbol> symbols) {
        final LinkedHashSet<String> result = new LinkedHashSet<>();
        for (final FunctionSymbol symbol : symbols) {
            result.add(symbol.getName());
        }
        return ImmutableCreator.create(result);
    }

    private boolean checkTerm(final TRSTerm t) {
        if (t instanceof TRSVariable) {
            return false;
        } else if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            final FunctionSymbol s = f.getRootSymbol();
            // s has to be a defined symbol.
            if (s.getArity() != 1 || !this.definedSymbols.contains(s)) {
                return false;
            } else {
                return this.checkConstructorPart(f.getArgument(0));
            }
        }
        return false;
    }

    private boolean checkConstructorPart(final TRSTerm t) {
        if (t instanceof TRSVariable) {
            return true;
        } else if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            final FunctionSymbol s = f.getRootSymbol();
            this.constructorSymbols.add(s);
            // s must not be a defined symbol.
            if (s.getArity() != 1 || this.definedSymbols.contains(s)) {
                return false;
            } else {
                return this.checkConstructorPart(f.getArgument(0));
            }
        }
        return false;
    }

    public ImmutableLinkedHashSet<IGeneralizedRule> getRules() {
        return this.rules;
    }

    public ImmutableLinkedHashSet<String> getDefinedSymbols() {
        return this.setOfDefinedSymbols;
    }

    public ImmutableLinkedHashSet<String> getConstructorSymbols() {
        return this.setOfConstructorSymbols;
    }

    /**
      * Transforms a(b(c(x))) into [a,b,c].
      * @param traceTerm a term of the a(b(c(x)))
      * @return list of strings
      */
    public static LinkedList<String> traceTermToList(final TRSTerm traceTerm) {
        final LinkedList<String> result = new LinkedList<>();
        TRSTerm current = traceTerm;
        while (current instanceof TRSFunctionApplication) {
            final TRSFunctionApplication currentFunc = (TRSFunctionApplication) current;
            final FunctionSymbol symbol = currentFunc.getRootSymbol();
            if (symbol.getArity() != 1) {
                assert false : "Not a trace term!";
            }
            result.addLast(symbol.getName());
            current = currentFunc.getArgument(0);
        }
        return result;
    }

    public FreshNameGenerator createFreshNameGenerator() {
        final FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        for (final IGeneralizedRule rule : this.rules) {
            this.lockNames(rule.getLeft(), fng);
            this.lockNames(rule.getRight(), fng);
        }
        return fng;
    }

    private void lockNames(final TRSTerm t, final FreshNameGenerator fng) {
        if (t instanceof TRSVariable) {
            final TRSVariable v = (TRSVariable) t;
            fng.lockName(v.getName());
        } else if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            fng.lockName(f.getRootSymbol().getName());
        }
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("Trace:");
        for (final IGeneralizedRule rule : this.rules) {
            sb.append("\n");
            sb.append(rule.toString());
        }
        return sb.toString();
    }

    public void export(final StringBuilder sb, final Export_Util eu) {
        for (final IGeneralizedRule rule : this.rules) {
            Trace.exportTraceRule(sb, eu, rule);
            sb.append(eu.linebreak());
        }
    }

    public static void exportTraceRule(final StringBuilder sb, final Export_Util eu, final IGeneralizedRule rule) {
        Trace.exportTraceTerm(rule.getLeft(), sb, eu);
        sb.append(eu.escape(" "));
        sb.append(eu.rightarrow());
        sb.append(eu.escape(" "));
        Trace.exportTraceTerm(rule.getRight(), sb, eu);
    }

    private static void exportTraceTerm(final TRSTerm t, final StringBuilder sb, final Export_Util eu) {
        if (t instanceof TRSVariable) {
            final TRSVariable v = (TRSVariable) t;
            sb.append(v.export(eu));
        } else if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            final FunctionSymbol s = f.getRootSymbol();
            sb.append(s.export(eu));
            sb.append(eu.escape(" "));
            final TRSTerm arg = f.getArgument(0);
            Trace.exportTraceTerm(arg, sb, eu);
        }
    }
}
