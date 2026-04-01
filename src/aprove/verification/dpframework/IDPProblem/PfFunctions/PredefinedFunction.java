package aprove.verification.dpframework.IDPProblem.PfFunctions;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker, cryingshadow
 * @param <D>
 * @version $Id$
 */
public abstract class PredefinedFunction<D extends Domain> extends PredefinedSemantics {

    /**
     * Predefined function symbols.<br><br>
     * It is important, that FALSE and TRUE have the same representation as in the idp.grammar and in the
     * PredefFunctionsNegPos.properties.
     * @author Martin Pluecker, cryingshadow
     * @version $Id$
     */
    public static enum Func {

        /**
         * Logical NOT.
         */
        Lnot("!", 1, false, true),

        /**
         * Logical AND.
         */
        Land("&&", 2, false, true),

        /**
         * Logical OR.
         */
        Lor("||", 2, false, true),

        /**
         * Bitwise NOT.
         */
        Bwnot("~", 1, true, false),

        /**
         * Bitwise AND.
         */
        Bwand("&", 2, true, false),

        /**
         * Bitwise XOR.
         */
        Bwxor("^", 2, true, false),

        /**
         * Bitwise OR.
         */
        Bwor("|", 2, true, false),

        /**
         * Cast.
         */
        Cast("cast", 1, true, false),

        /**
         * Addition.
         */
        Add("+", 2, true, false),

        /**
         * Subtraction.
         */
        Sub("-", 2, true, false),

        /**
         * Multiplication.
         */
        Mul("*", 2, true, false),

        /**
         * Division.
         */
        Div("/", 2, true, false),

        /**
         * Modulus.
         */
        Mod("%", 2, true, false),

        /**
         * Unary minus.
         */
        UnaryMinus("-", 1, true, false),

        /**
         * Greater than.
         */
        Gt(">", 2, true, false),

        /**
         * Greater than or equal to.
         */
        Ge(">=", 2, true, false),

        /**
         * Equal to.
         */
        Eq("=", 2, true, false),

        /**
         * Unequal to.
         */
        Neq("!=", 2, true, false),

        /**
         * Less than or equal to.
         */
        Le("<=", 2, true, false),

        /**
         * Less than.
         */
        Lt("<", 2, true, false);

        /**
         * The name of the function symbol.
         */
        final private String name;

        /**
         * The function symbol's arity.
         */
        final private int arity;

        /**
         * Is the function symbol representing an integer function?
         */
        final private boolean isIntFunction;

        /**
         * Is the function symbol representing a boolean function?
         */
        final private boolean isBooleanFunction;

        /**
         * @param name The name of the function symbol.
         * @param arity The function symbol's arity.
         * @param isIntFunction Is the function symbol representing an integer function?
         * @param isBooleanFunction Is the function symbol representing a boolean function?
         */
        private Func(String name, int arity, boolean isIntFunction, boolean isBooleanFunction) {
            this.name = name;
            this.arity = arity;
            this.isIntFunction = isIntFunction;
            this.isBooleanFunction = isBooleanFunction;
        }

        /**
         * @return The function symbol.
         */
        public FunctionSymbol asFunctionSymbol() {
            return FunctionSymbol.create(this.name, this.arity);
        }

        /**
         * @return The arity.
         */
        public int getArity() {
            return this.arity;
        }

        /**
         * @return The name.
         */
        public String getName() {
            return this.name;
        }

        /**
         * @return Is the function symbol representing an integer function?
         */
        public boolean isIntFunction() {
            return this.isIntFunction;
        }

        /**
         * @return Is the function symbol representing a boolean function?
         */
        public boolean isBooleanFunction() {
            return this.isBooleanFunction;
        }

    }

    protected final PredefinedFunction.Func func;

    protected final ImmutableList<? extends D> domains;

    protected final Domain resultDomain;

    /**
     * my abstract rule for IUsableRules
     * e.g. x / y -> x / y
     */
    private volatile GeneralizedRule abstractRule;

    protected PredefinedFunction(PredefinedFunction.Func func, ImmutableList<? extends D> domains) {
        super(func.getArity());
        if (Globals.useAssertions) {
            assert(domains.size() == func.getArity()) : "domain list must correspond to arity";
        }
        this.func = func;
        this.domains = domains;
        this.resultDomain = this.determineResultDomain();
    }

    /**
     * @param t - the term that should be matched with the lhs of a predefined rule
     * @param predefinedMap TODO
     * @return true iff the given term can be matched with the lhs of any
     * predefined rule for this predefined function symbol
     */
    public abstract boolean canMatchPredefLhs(TRSTerm t, IDPPredefinedMap predefinedMap);

    /**
     * checks whether t is a lhs of a rule for this predefined function
     * @param t
     * @param predefinedMap TODO
     */
    public abstract boolean isPredefLhs(TRSTerm t, IDPPredefinedMap predefinedMap);

    /**
     * If the predefined function can be represented as a finite rule set, this function
     * returns the corresponding rule set.
     * @param fs TODO
     * @return A finite set of rules that represent the predefined function if one exists, null otherwise.
     */
    public abstract ImmutableSet<GeneralizedRule> getFiniteRuleSet(FunctionSymbol fs);

    /**
     * Use this rule e.g. for computation of usable rules
     * @return An abstract rule e.g. x1 + x2 -> x3
     */
    public GeneralizedRule getAbstractRule(FunctionSymbol rootSymbol) {
        if (this.abstractRule == null) {
            synchronized(this) {
                if (this.abstractRule == null) {
                    FunctionSymbol symbol = rootSymbol;
                    ArrayList<TRSTerm> arguments = new ArrayList<TRSTerm>(this.arity);
                    for (int i = 0; i < this.arity; i++) {
                        arguments.add(TRSTerm.createVariable(TRSTerm.STANDARD_PREFIX + (TRSTerm.STANDARD_NUMBER + i)));
                    }
                    TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(symbol, ImmutableCreator.create(arguments));
                    TRSTerm rhs = TRSTerm.createVariable(TRSTerm.STANDARD_PREFIX + (TRSTerm.STANDARD_NUMBER + this.arity));
                    this.abstractRule = GeneralizedRule.create(lhs, rhs, lhs, rhs);
                }
            }
        }
        return this.abstractRule;
    }

    /**
     * Determines if the predefined function can be represented as a finite rule set.
     * @return true iff a finite rule set exists that represents the predefined function.
     */
    public abstract boolean hasFiniteRuleSet();

    /**
     * True, iff this predefined function executes bitwise operations (bitwise
     * and, or, not, xor, ...)
     */
    public boolean isBitwise() {
        return false;
    }

    /**
     * True, iff this predefined function is an arithmetic one (i.e. maps
     * integers to integers: add, sub, mul, div, ...)
     */
    public boolean isArithmetic() {
        return false;
    }

    /**
     * True, iff this predefined function is a relation (i.e maps integers
     * to booleans: greater, greater_equals, ...)
     */
    public boolean isRelation() {
        return false;
    }

    @Override
    public boolean isConstructor() {
        return false;
    }

    @Override
    public boolean isFunction() {
        return true;
    }

    /**
     * True, iff this predefined function is a boolean one (i.e. maps booleans
     * to booleans: logical and, or, not)
     */
    public boolean isBoolean() {
        return false;
    }

    public Func getFunc() {
        return this.func;
    }

    public ImmutableList<? extends D> getDomains() {
        return this.domains;
    }

    public Domain getResultDomain() {
        return this.resultDomain;
    }

    protected abstract Domain determineResultDomain();

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        sb.append(this.func.name());
        sb.append(": (");
        for (Domain dom : this.domains) {
            sb.append(dom.export(o));
            sb.append(", ");
        }
        sb.setLength(sb.length() - 2);
        sb.append(") -> ");
        sb.append(this.getResultDomain().export(o));
        return sb.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

}
