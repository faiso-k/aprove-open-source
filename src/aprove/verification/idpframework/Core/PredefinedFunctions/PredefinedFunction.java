package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public abstract class PredefinedFunction<I extends SemiRing<I>, R extends SemiRing<R>> extends
        PredefinedSemantics<R> {

    public static enum Func {
        /*
         * It is important, that FALSE and TRUE have the same representation as
         * in the idp.grammar and in the PredefFunctionsNegPos.properties
         */
        Lnot("!", 1, false, true), Land("&&", 2, false, true), Lor("||", 2,
                false, true), Bwnot("~", 1, true, false), Bwand("&", 2, true,
                false), Bwxor("^", 2, true, false), Bwor("|", 2, true, false),
        Cast("cast", 1, true, false), Add("+", 2, true, false), Sub("-", 2,
                true, false), Mul("*", 2, true, false),
        Div("/", 2, true, false), Mod("%", 2, true, false), UnaryMinus("-", 1,
                true, false), Gt(">", 2, true, false),
        Ge(">=", 2, true, false), Eq("=", 2, true, false), Neq("!=", 2, true,
                false), Le("<=", 2, true, false), Lt("<", 2, true, false), ;

        final private String name;
        final private int arity;
        final private boolean isIntFunction;
        final private boolean isBooleanFunction;

        private Func(final String name, final int arity,
                final boolean isIntFunction, final boolean isBooleanFunction) {
            this.name = name;
            this.arity = arity;
            this.isIntFunction = isIntFunction;
            this.isBooleanFunction = isBooleanFunction;
        }

        public int getArity() {
            return this.arity;
        }

        public String getName() {
            return this.name;
        }

        public boolean isBooleanFunction() {
            return this.isBooleanFunction;
        }

        public boolean isIntFunction() {
            return this.isIntFunction;
        }

    }

    protected final PredefinedFunction.Func func;
    protected final ImmutableList<? extends SemiRingDomain<I>> domains;
    protected SemiRingDomain<R> resultDomain;

    /**
     * my abstract rule for IUsableRules e.g. x / y -> x / y
     */
    private volatile UnconditionalIRule abstractRule;

    protected PredefinedFunction(final PredefinedFunction.Func func,
            final ImmutableList<? extends SemiRingDomain<I>> domains) {
        super(func.getArity());
        if (Globals.useAssertions) {
            assert (domains.size() == func.getArity()) : "domain list must correspond to arity";
        }
        this.func = func;
        this.domains = domains;
        this.resultDomain = this.determineResultDomain();
    }

    /**
     * @param t - the ITerm<?> that should be matched with the lhs of a predefined
     * rule
     * @return true iff the given ITerm<?> can be matched with the lhs of any
     * predefined rule for this predefined function symbol
     */
    public abstract boolean canMatchPredefLhs(ITerm<?> t);

    protected abstract SemiRingDomain<R> determineResultDomain();

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        sb.append(this.func.name());
        sb.append(": (");
        for (final SemiRingDomain<I> dom : this.domains) {
            sb.append(dom.export(o));
            sb.append(", ");
        }
        sb.setLength(sb.length() - 2);
        sb.append(") -> ");
        sb.append(this.getResultDomain().export(o));
    }

    /**
     * Use this rule e.g. for computation of usable rules
     * @return An abstract rule e.g. x1 + x2 -> x3
     */
    public UnconditionalIRule getAbstractRule(final IFunctionSymbol<R> rootSymbol) {
        if (this.abstractRule == null) {
            synchronized (this) {
                if (this.abstractRule == null) {
                    final IFunctionSymbol<R> symbol = rootSymbol;
                    final ArrayList<ITerm<?>> arguments =
                        new ArrayList<ITerm<?>>(this.arity);
                    for (int i = 0; i < this.arity; i++) {
                        arguments.add(ITerm.createVariable(
                            ITerm.STANDARD_PREFIX + (ITerm.STANDARD_NUMBER + i),
                            this.domains.get(i)));
                    }
                    final IFunctionApplication<R> lhs =
                        ITerm.createFunctionApplication(symbol,
                            ImmutableCreator.create(arguments));
                    final ITerm<R> rhs =
                        ITerm.createVariable(ITerm.STANDARD_PREFIX
                            + (ITerm.STANDARD_NUMBER + this.arity),
                            this.getResultDomain());
                    this.abstractRule = IRuleFactory.create(lhs, rhs, lhs, rhs);
                }
            }
        }
        return this.abstractRule;
    }

    @Override
    public ImmutableList<? extends SemiRingDomain<I>> getDomains() {
        return this.domains;
    }

    /**
     * If the predefined function can be represented as a finite rule set, this
     * function returns the corresponding rule set.
     * @param fs TODO
     * @return A finite set of rules that represent the predefined function if
     * one exists, null otherwise.
     */
    public abstract ImmutableSet<? extends IRule> getFiniteRuleSet(IFunctionSymbol<R> fs);

    public Func getFunc() {
        return this.func;
    }

    @Override
    public SemiRingDomain<R> getResultDomain() {
        return this.resultDomain;
    }

    /**
     * DeITerm<?>ines if the predefined function can be represented as a finite
     * rule set.
     * @return true iff a finite rule set exists that represents the predefined
     * function.
     */
    public abstract boolean hasFiniteRuleSet();

    /**
     * True, iff this predefined function is an arithmetic one (i.e. maps
     * integers to integers: add, sub, mul, div, ...)
     */
    public boolean isArithmetic() {
        return false;
    }

    /**
     * True, iff this predefined function executes bitwise operations (bitwise
     * and, or, not, xor, ...)
     */
    public boolean isBitwise() {
        return false;
    }

    /**
     * True, iff this predefined function is a boolean one (i.e. maps booleans
     * to booleans: logical and, or, not)
     */
    public boolean isBoolean() {
        return false;
    }

    @Override
    public boolean isConstructor() {
        return false;
    }

    /**
     * checks whether t is a lhs of a rule for this predefined function
     * @param t
     */
    public abstract boolean isPredefLhs(ITerm<?> t);

    /**
     * True, iff this predefined function is a relation (i.e maps integers to
     * booleans: greater, greater_equals, ...)
     */
    public boolean isRelation() {
        return false;
    }
}
