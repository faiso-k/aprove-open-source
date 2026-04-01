/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem;

import java.util.*;

import aprove.input.Programs.idp.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Helper class for saving IDP or ITRS problems as text.
 *
 * <p>
 * The public method <code>toAProVE_IDP()</code> creates the source code
 * and takes care of the following things:
 * </p>
 * <ul>
 * <li>Rename variables, so there is no name which corresponds to a
 *     function symbol as well as to a variable</li>
 * <li>Rename function symbols, which are not valid tokens in the text
 *     format</li>
 * <li>Take care of infix symbols</li>
 * </ul>
 * @author noschinski
 *
 */
public class SaveProblemHelper<T extends GeneralizedRule> {

    /**
     * Used for generating new variable names.
     */
    final private FreshVarGenerator fvg;

    /**
     * Used to determine which function symbols are predefined.
     */
    final private IDPPredefinedMap predefinedMap;

    private SaveProblemHelper(Collection<String> usedNames, IDPPredefinedMap predefinedMap) {
        FreshNameGenerator fng = new FreshNameGenerator(usedNames,
                FreshNameGenerator.APPEND_NUMBERS);
        this.fvg = new FreshVarGenerator(fng);
        this.predefinedMap = predefinedMap;
    }

    protected static <Q extends GeneralizedRule> SaveProblemHelper<Q> create(Iterable<Q> rules,
            IDPPredefinedMap predefinedMap) {
        Collection<String> used = new LinkedList<String>();
        used.addAll(CollectionUtils.getNames(CollectionUtils.getFunctionSymbols(rules)));

        return new SaveProblemHelper<Q>(used, predefinedMap);
    }

    /**
     * Returns a (eventually escaped) name for fs, which is valid in the text
     * format. Leaves predefined function symbols alone.
     */
    protected String getEscapedName(FunctionSymbol fs) {
        if (this.predefinedMap.isPredefined(fs)) {
            return fs.getName();
        } else {
            return EscapeHandler.escape(fs.getName());
        }
    }

    /**
     * Returns a (eventually escaped) name for v, which is valid in the text
     * format. Leaves predefined function symbols alone.
     */
    protected static String getEscapedName(TRSVariable v) {
        return EscapeHandler.escape(v.getName());
    }

    /**
     * Replace all variables in rule by variables with
     * not yet used names.
     */
    protected GeneralizedRule uniqueVariableNames(GeneralizedRule rule) {
        TRSFunctionApplication l = rule.getLeft();
        TRSTerm r = rule.getRight();

        return GeneralizedRule.create(
                l.renameVariables(this.fvg),
                r.renameVariables(this.fvg));
    }

    /** Applies uniqueVariableNames to every rule */
    protected Set<GeneralizedRule> uniqueVariableNames(Iterable<? extends GeneralizedRule> rules) {
        Set<GeneralizedRule> newRules = new LinkedHashSet<GeneralizedRule>();
        for(GeneralizedRule r : rules) {
            newRules.add(this.uniqueVariableNames(r));
        }
        return newRules;
    }

    /**
     * Formats a GeneralizedRule in valid IDP syntax, with indentation and new line.
     *
     * @param s Result is appended here
     * @param r GeneralizedRule to format.
     */
    protected void formatRule(StringBuilder s, GeneralizedRule r) {
        s.append("    ");
        this.formatTerm(s, r.getLeft());
        s.append(" -> ");
        this.formatTerm(s, r.getRight());
        s.append('\n');
    }

    /**
     * Formats a Term in valid IDP syntax.
     *
     * @param s Result is appended here
     * @param t Term to format
     */
    protected void formatTerm(StringBuilder s, TRSTerm t) {
        if (t.isVariable()) {
            s.append(SaveProblemHelper.getEscapedName((TRSVariable)t));
            return;
        }

        TRSFunctionApplication fa = (TRSFunctionApplication)t;
        FunctionSymbol rootSym = fa.getRootSymbol();

        /* All predefined function symbols of arity two are infix symbols. */
        if (this.predefinedMap.isPredefined(rootSym) && rootSym.getArity() == 2) {
            s.append('(');
            this.formatTerm(s, fa.getArgument(0));
            s.append(' ');
            s.append(rootSym.getName());
            s.append(' ');
            this.formatTerm(s, fa.getArgument(1));
            s.append(')');
        } else if (rootSym.getArity() == 0) {
            s.append(this.getEscapedName(rootSym));
        } else {
            s.append(this.getEscapedName(rootSym));
            s.append('(');
            boolean first = true;
            for (TRSTerm sub : fa.getArguments()) {
                if (!first) {
                    s.append(", ");
                }
                first = false;

                this.formatTerm(s, sub);
            }
            s.append(')');
        }
    }

    /**
     * Generates an IDP/ITRS source text.
     * @param R Rules, must not be <code>null</code>.
     * @param P Pairs, may be <code>null</code>.
     * @param predefMap Holds information on which of the function symbols in
     *  R and P are predefined.
     * @return
     */
    public static <T extends GeneralizedRule> String toAProVE_IDP(Collection<T> R, Collection<T> P, IDPPredefinedMap predefMap) {
        if (P == null) {
            P = java.util.Collections.<T>emptySet();
        }

        StringBuilder s1 = new StringBuilder();
        StringBuilder s2 = new StringBuilder();

        SaveProblemHelper<T> pe = SaveProblemHelper.create(
                IterableConcatenator.create(P, R), predefMap);

        // FIXME: Add method to replace neg. integers by unary minus + pos. integer
        Set<GeneralizedRule> exportP = pe.uniqueVariableNames(P);
        Set<GeneralizedRule> exportR = pe.uniqueVariableNames(R);

        Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
        if (!exportP.isEmpty()) {
            s2.append("(PAIRS\n");
            for (GeneralizedRule pair : exportP) {
                vars.addAll(pair.getVariables());
                pe.formatRule(s2, pair);
            }
            s2.append(")\n");
        }
        s2.append("(RULES\n");
        for (GeneralizedRule rule : exportR) {
            vars.addAll(rule.getVariables());
            pe.formatRule(s2, rule);
        }
        s2.append(")\n");

        s1.append("(VAR");
        for (TRSVariable var : vars) {
            s1.append(" "+ SaveProblemHelper.getEscapedName(var));
        }
        s1.append(")\n");

        s1.append(s2);
        return s1.toString();
    }

}
