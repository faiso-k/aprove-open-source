/**
 * @author prometheus
 * @version $Id$
 */

package aprove.verification.dpframework.CLSProblem;

import java.io.*;
import java.util.*;

import aprove.input.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This class provides the rules for the prefedinfed function symbols of java
 * programs. This class uses the neg-pos-representation for integers.
 *
 * @author prometheus
 *
 */
public class PredefinedFunctionsManagerNegPos {
    private static final Properties predefProps;

    /** Symbol for integer zero */
    private static final FunctionSymbol default0;

    /** Constructor for numbers */
    private static final FunctionSymbol defaultS;

    /** Constructor for negative integer numbers */
    private static final FunctionSymbol defaultNeg;

    /** Constructor for positive integer numbers */
    private static final FunctionSymbol defaultPos;

    private static final FunctionSymbol actual0;

    private static final FunctionSymbol actualS;

    private static final FunctionSymbol actualPos;

    private static final FunctionSymbol actualNeg;

    private static final TRSFunctionApplication zeroApp;

    static {

        // Load the file with the function symbol declarations
        predefProps = new Properties();
        try {
            PropertyLoader.fromXMLResource(
                PredefinedFunctionsManagerNegPos.predefProps,
                CLSProblem.class,
                "Properties/PredefFunctionsNegPos.properties"
            );
        }
        catch (IOException e) {
            System.out.println(e);
            e.printStackTrace();
            throw new RuntimeException("Predefined rules cannot be found or is damaged");
        }

        actual0 = FunctionSymbol.create(PredefinedFunctionsManagerNegPos.predefProps.getProperty("0", "0").trim(), 0);
        actualS = FunctionSymbol.create(PredefinedFunctionsManagerNegPos.predefProps.getProperty("s", "s").trim(), 1);
        actualPos =
            FunctionSymbol.create(PredefinedFunctionsManagerNegPos.predefProps.getProperty("pos", "pos").trim(), 1);
        actualNeg =
            FunctionSymbol.create(PredefinedFunctionsManagerNegPos.predefProps.getProperty("neg", "neg").trim(), 1);

        default0 = FunctionSymbol.create("0", 0);
        defaultS = FunctionSymbol.create("s", 1);
        defaultPos = FunctionSymbol.create("pos", 1);
        defaultNeg = FunctionSymbol.create("neg", 1);

        zeroApp = TRSTerm.createFunctionApplication(PredefinedFunctionsManagerNegPos.actual0, TRSTerm.EMPTY_ARGS);

    }

    private PredefinedFunctionsManagerNegPos() {

    }

    /**
     * Returns an array of function symbols corresponding to the semantics of
     * the specified JExpression object
     *
    public static final FunctionSymbol[] getFunctionSymbol(Class<? extends JExpression> classs) {
        FunctionSymbol[] funcSyms = expressionFunctionSymbolMap.get(classs);
        if (funcSyms == null) {
            String value = predefProps.getProperty(classs.getSimpleName());
            if (Globals.useAssertions) {
                assert value != null : "There is no function symbol for " + classs;
            }
            String[] funcSymDecls = value.split(",");
            funcSyms = new FunctionSymbol[funcSymDecls.length];
            for (int i = 0; i < funcSymDecls.length; i++) {
                String funcSymDecl = funcSymDecls[i];
                String[] funcSymDeclNameArity = funcSymDecl.split("/");
                String funcSymName = funcSymDeclNameArity[0].trim();
                int funcSymArity = Integer.parseInt(funcSymDeclNameArity[1].trim());
                funcSyms[i] = FunctionSymbol.create(funcSymName, funcSymArity);
            }
            expressionFunctionSymbolMap.put(classs, funcSyms);
        }
        return funcSyms;
    }*/

    /**
     * Returns the set of rules needed to calculate the function symbol's
     * semantic.
     *
     * @param funcSym
     *            The function symbols whose rules shall be returned
     */
    public static final Pair<Set<Rule>,FunctionSymbol> generateRules(FunctionSymbol funcSym) {
        String s = PredefinedFunctionsManagerNegPos.predefProps.getProperty(funcSym.getName());
        if (s == null) {
            throw new RuntimeException("No rules found for function symbol " + funcSym);
        }
        s = s.split("\n")[1].trim();
        String[] nameAndArity = s.split("/");
        String name = nameAndArity[0].trim();
        Integer arity = Integer.parseInt(nameAndArity[1].trim());
        funcSym = FunctionSymbol.create(name, arity);
        return new Pair<Set<Rule>,FunctionSymbol>(PredefinedFunctionsManagerNegPos.generateRulesDirectly(funcSym),funcSym);
    }

    /**
     * Supplementary function for generateRules(FunctionSymbol funcSym). Keeps
     * track of function symbols that have been handled already.
     */
    private static final Set<Rule> generateRulesDirectly(FunctionSymbol funcSym) {
        // TODO cache if neccessary

        Set<Rule> retSet = new LinkedHashSet<Rule>();
        // Retrieve rules for this function symbol
        String s = PredefinedFunctionsManagerNegPos.predefProps.getProperty(funcSym.getName());
        if (s == null) {
            throw new RuntimeException("No rules found for function symbol " + funcSym);
        }
        s = s.replaceAll(PredefinedFunctionsManagerNegPos.default0.getName(), PredefinedFunctionsManagerNegPos.actual0.getName());
        s = s.replaceAll(PredefinedFunctionsManagerNegPos.defaultS.getName(), PredefinedFunctionsManagerNegPos.actualS.getName());
        s = s.replaceAll(PredefinedFunctionsManagerNegPos.defaultPos.getName(), PredefinedFunctionsManagerNegPos.actualPos.getName());
        s = s.replaceAll(PredefinedFunctionsManagerNegPos.defaultNeg.getName(), PredefinedFunctionsManagerNegPos.actualNeg.getName());

        // FIXME: We need to make the predefined symbols unique, so no
        // side effects can occur!

        // Parse the rule string
        String[] ruleStrings = s.split("\n");
        String variables = ruleStrings[1].trim();
        variables = variables.substring(1, variables.length() - 1);
        String invocations = ruleStrings[2].trim();
        invocations = invocations.substring(1, invocations.length() - 1);

        // Add rules to return set
        for (int i = 3; i < ruleStrings.length; i++) {
            String ruleString = ruleStrings[i].trim();
            if (ruleString.contains("->")) {
                String[] lhsrhs = ruleString.split("->");
                TRSFunctionApplication lhs = (TRSFunctionApplication) EasyInput.parseTerm(variables, lhsrhs[0].trim());
                TRSTerm rhs = EasyInput.parseTerm(variables, lhsrhs[1].trim());
//                JavaGlobals.debug(lhs + " -> " + rhs);
                retSet.add(Rule.create(lhs, rhs));
            }
        }

        // Add rules of the invocated functions
        if (invocations.length() > 0) {
            for (String invocation : invocations.split(",")) {
                String[] nameAndArity = invocation.split("/");
                String name = nameAndArity[0].trim();
                Integer arity = Integer.parseInt(nameAndArity[1].trim());
                retSet.addAll(PredefinedFunctionsManagerNegPos.generateRulesDirectly(FunctionSymbol.create(name, arity)));
            }
        }
        return retSet;
    }

    /**
     * Calculates the term representation of the given number using the
     * neg/pos-representation. Zero will be represented as pos(0)
     */
    public static final TRSFunctionApplication numberToTerm(int number) {
        TRSFunctionApplication retFunc = PredefinedFunctionsManagerNegPos.zeroApp;

        int n = Math.abs(number);
        for (int i = 0; i < n; i++) {
            retFunc = TRSTerm.createFunctionApplication(PredefinedFunctionsManagerNegPos.actualS, new TRSTerm[] { retFunc });
        }
        if (number >= 0) {
            retFunc = TRSTerm.createFunctionApplication(PredefinedFunctionsManagerNegPos.actualPos, new TRSTerm[] { retFunc });
        }
        else {
            retFunc = TRSTerm.createFunctionApplication(PredefinedFunctionsManagerNegPos.actualNeg, new TRSTerm[] { retFunc });
        }
        return retFunc;
    }

    public static final boolean hasRules(FunctionSymbol funcSym) {
        return PredefinedFunctionsManagerNegPos.predefProps.containsKey(funcSym.getName());
    }

}
