/**
 * @author prometheus
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfManager;

import java.io.*;
import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This class provides the rules for the predefined function symbols of java
 * programs. This class uses the neg-pos-representation for integers.
 *
 * Only unrestricted integers (Z, domain suffix "z") are supported.
 *
 * @author prometheus
 * @author noschinski
 * @version $Id$
 */
public class PredefinedFunctionsManagerNegPos extends PredefinedFunctionsManager {

    private static final Properties predefProps;

    /**
     * Maximal absolute value of an integer which can be converted
     * into NegPos representation.
     */
    private final int maxConvInt;

    /**
     * maxConvInt, stored as BigInteger.
     */
    private final BigInteger maxConvBigInt;

    static {

        // Load the file with the function symbol declarations
        predefProps = new Properties();
        try {
            PropertyLoader.fromXMLResource(PredefinedFunctionsManagerNegPos.predefProps, IDPProblem.class, "Properties/PredefFunctionsNegPos.properties");
        }
        catch (final IOException e) {
            System.out.println(e);
            e.printStackTrace();
            throw new RuntimeException("Predefined rules cannot be found or is damaged");
        }

    }

    /* ------------- NON-STATIC PROPERTIES ---------------- */
    private final FreshNameGenerator freshNames;

    /** Symbol for integer zero */
    private final FunctionSymbol sym0;

    /** Constructor for numbers */
    private final FunctionSymbol symS;

    /** Constructor for negative integer numbers */
    private final FunctionSymbol symNeg;

    /** Constructor for positive integer numbers */
    private final FunctionSymbol symPos;

    /** Term representing integer zero */
    private final TRSFunctionApplication zeroApp;

    private PredefinedFunctionsManagerNegPos(
        IDPPredefinedMap predefinedMap,
        FreshNameGenerator freshNames,
        int maxAbsValue
    ) {
        super(predefinedMap);
        this.freshNames = freshNames;
        this.maxConvInt = maxAbsValue;
        this.maxConvBigInt = BigInteger.valueOf(maxAbsValue);
        this.sym0 = FunctionSymbol.create(freshNames.getFreshName("0", true), 0);
        this.symS = FunctionSymbol.create(freshNames.getFreshName("s", true), 1);
        this.symNeg = FunctionSymbol.create(freshNames.getFreshName("neg", true), 1);
        this.symPos = FunctionSymbol.create(freshNames.getFreshName("pos", true), 1);
        this.zeroApp = TRSTerm.createFunctionApplication(this.sym0, TRSTerm.EMPTY_ARGS);
    }

    /**
     * Creates a new manager which avoids all names used in <code>fSymHavers</code>
     * for newly created Terms and which only converts number with an absolute value
     * up to <code>maxAbsValue</code>.
     */
    public static PredefinedFunctionsManagerNegPos create(
        IDPPredefinedMap predefinedMap,
        Iterable<? extends HasFunctionSymbols> fSymHavers,
        int maxAbsValue
    ) {
        return
            new PredefinedFunctionsManagerNegPos(
                predefinedMap,
                new FreshNameGenerator(
                    CollectionUtils.getNames(CollectionUtils.getFunctionSymbols(fSymHavers)),
                    FreshNameGenerator.PROLOG_VARS
                ),
                maxAbsValue
            );
    }

    /**
     * Creates a new manager which avoids all names used in <code>fn</code>
     * for newly created Terms and which only converts number with an absolute value
     * up to <code>maxAbsValue</code>.
     */
    public static PredefinedFunctionsManagerNegPos create(
        IDPPredefinedMap predefinedMap,
        FreshNameGenerator fn,
        int maxAbsValue
    ) {
        return new PredefinedFunctionsManagerNegPos(predefinedMap,
            fn, maxAbsValue);
    }

    /**
     * Returns the property value for a function symbol.
     */
    protected String getPropertyForFuncsym(final FunctionSymbol funcSym) {
        final PredefinedSemantics sem = this.idpPredefinedMap.getPredefinedSemantics(funcSym);
        if (sem != null) {
            if (sem.isFunction()) {
                final PredefinedFunction<? extends Domain> func = (PredefinedFunction<? extends Domain>) sem;
                final StringBuilder name = new StringBuilder();
                name.append(func.getFunc().getName());
                for (final Domain dom : func.getDomains()) {
                    name.append(DomainFactory.SUFFIX_SEPERATOR);
                    name.append(dom.getSuffix());
                }
                name.append("/");
                name.append(func.getArity());
                return PredefinedFunctionsManagerNegPos.predefProps.getProperty(name.toString());
            } else {
                final PredefinedConstructor constr = (PredefinedConstructor) sem;
                final StringBuilder name = new StringBuilder();
                name.append(constr.getSym().getName());
                name.append(DomainFactory.SUFFIX_SEPERATOR);
                name.append(constr.getDomain().getSuffix());
                name.append("/");
                name.append(constr.getArity());
                return PredefinedFunctionsManagerNegPos.predefProps.getProperty(name.toString());
            }
        }
        return null;
    }


    /**
     * Returns the set of rules needed to calculate the function symbol's
     * semantic.
     *
     * @param funcSym
     *            The function symbols whose rules shall be returned
     */
    @Override
    protected Pair<Set<Rule>,FunctionSymbol> generateRules(final FunctionSymbol funcSym) {
        String s = this.getPropertyForFuncsym(funcSym);
        // We want to skip internal rules. All these have a variable
        // declaration ("[...]") first.
        if (s == null || s.trim().charAt(0) == '[') {
            throw new RuntimeException("No rule for predefined symbol "
                    + funcSym.getName() + " in property file!");
        }
        s = s.split("\n")[1].trim();
        final int idx = s.lastIndexOf('/');
        final String name = s.substring(0, idx).trim();
        final Integer arity = Integer.parseInt(s.substring(idx+1).trim());
        if (Globals.useAssertions) {
            assert(funcSym.getArity() == arity);
        }
        final FunctionSymbol funcSymFresh =
            FunctionSymbol.create(this.freshNames.getFreshName(name, true), arity);
        return new Pair<Set<Rule>,FunctionSymbol>(this.generateRulesDirectly(s),funcSymFresh);
    }

    /**
     * Supplementary function for generateRules(FunctionSymbol funcSym). Keeps
     * track of function symbols that have been handled already.
     */
    private final Set<Rule> generateRulesDirectly(final String propKey) {
        // TODO cache if necessary

        final Set<Rule> retSet = new LinkedHashSet<Rule>();
        // Retrieve rules for this function symbol
        final String s = PredefinedFunctionsManagerNegPos.predefProps.getProperty(propKey);
        if (s == null) {
            throw new RuntimeException("No rules found for function symbol " + propKey);
        }
        // Parse the rule string
        final String[] ruleStrings = s.split("\n");
        String variables = ruleStrings[1].trim();
        variables = variables.substring(1, variables.length() - 1);
        String invocationsStr = ruleStrings[2].trim();
        invocationsStr = invocationsStr.substring(1, invocationsStr.length() - 1);

        String[] invocations = {};
        if (invocationsStr.length() > 0) {
            invocations = invocationsStr.split(",");
        }

        // Add rules to return set
        for (int i = 3; i < ruleStrings.length; i++) {
            final String ruleString = ruleStrings[i].trim();
            if (ruleString.contains("->")) {
                final String[] lhsrhs = ruleString.split("->");
                TRSFunctionApplication lhs = (TRSFunctionApplication) EasyInput.parseTerm(variables, lhsrhs[0].trim());
                TRSTerm rhs = EasyInput.parseTerm(variables, lhsrhs[1].trim());
                lhs = this.mapTermFreshnames(lhs);
                rhs = this.mapTermFreshnames(rhs);
                retSet.add(Rule.create(lhs, rhs));
            }
        }

        // Add rules of the invoked functions
        for (final String invocation : invocations) {
            retSet.addAll(this.generateRulesDirectly(invocation.trim()));
        }
        return retSet;
    }

    /**
     * Calculates the term representation of the given number using the
     * neg/pos-representation. Zero will be represented as pos(0).
     */
    private final TRSFunctionApplication numberToTerm(final int number)
            throws IntOutOfRangeException {
        TRSFunctionApplication retFunc = this.zeroApp;

        final int n = Math.abs(number);
        if (n > this.maxConvInt) {
            throw new IntOutOfRangeException(number, this.maxConvInt);
        }
        for (int i = 0; i < n; i++) {
            retFunc = TRSTerm.createFunctionApplication(this.symS, new TRSTerm[] { retFunc });
        }
        if (number >= 0) {
            retFunc = TRSTerm.createFunctionApplication(this.symPos, new TRSTerm[] { retFunc });
        } else {
            retFunc = TRSTerm.createFunctionApplication(this.symNeg, new TRSTerm[] { retFunc });
        }
        return retFunc;
    }

    /**
     * Calculates the term representation of the given number using the
     * neg/pos-representation. Zero will be represented as pos(0).
     */
    @Override
    protected final TRSFunctionApplication numberToTerm(final BigInteger number)
            throws IntOutOfRangeException {
        if (number.abs().compareTo(this.maxConvBigInt) > 0) {
            throw new IntOutOfRangeException(number, this.maxConvBigInt);
        }

        return this.numberToTerm(number.intValue());
    }

    /**
     * Replaces all symbols in a term by fresh names.
     */
    private TRSTerm mapTermFreshnames(final TRSTerm term) {
        if (term.isVariable()) {
            return term;
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication)term;
            final FunctionSymbol oldRoot = fa.getRootSymbol();

            final String newName = this.freshNames.getFreshName(oldRoot.getName(), true);
            final FunctionSymbol newRoot =
                FunctionSymbol.create(newName, oldRoot.getArity());

            final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(oldRoot.getArity());
            for (final TRSTerm a : fa.getArguments()) {
                newArgs.add(this.mapTermFreshnames(a));
            }

            return TRSTerm.createFunctionApplication(newRoot, ImmutableCreator.create(newArgs));
        }
    }

    /**
     * Replaces all symbols in a function application by fresh names.
     */
    private TRSFunctionApplication mapTermFreshnames(final TRSFunctionApplication fa) {
        return (TRSFunctionApplication)this.mapTermFreshnames((TRSTerm)fa);
    }

}
