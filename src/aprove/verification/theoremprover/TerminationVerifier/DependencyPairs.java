package aprove.verification.theoremprover.TerminationVerifier;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * This class provides a method to determine the dependency pairs of a given set of rules.
 * @author Carsten Pelikan, Peter Schneider-Kamp, Stephan Falke
 * @version $Id$
 */
public class DependencyPairs extends LinkedHashSet<Rule> implements HTML_Able, LaTeX_Able, PLAIN_Able {

    private static ConstructorSymbol getTupleSymbol(FreshNameGenerator fng, AlgebraTerm t) {
        DefFunctionSymbol def = (DefFunctionSymbol)t.getSymbol();
        String newName = fng.getFreshName(def.getName(), true);
    TupleSymbol res = TupleSymbol.create(newName, def.getArgSorts(), def.getSort(), def);
    // INFIX?
    res.setFixity(def.getFixity(), def.getFixityLevel());
    return res;
    }

    public DependencyPairs() {
        super();
    }

    /**
     * Computes the dependency pairs using Tuple Symbols for all defined function symbols.
     * @param prog The program to determine the dependency pairs for.
     * @return The dependency pairs for the given program.
     */
    public static DependencyPairs create(Program prog) {
        return DependencyPairs.create(prog.getRules(), prog.getSignature(), true, false, null);
    }

    /**
     * Computes the dependency pairs.
     * @param prog The program to determine the dependency pairs for.
     * @param tuple Specifies whether to use Tuple Symbols.
     * @param onlyFree Specifies whether only free function symbols get TupleSymbols.
     * @param free Specifies the free function symbols.
     * @return The dependency pairs for the given program.
     */
    public static DependencyPairs create(Program prog, boolean tuple, boolean onlyFree, Set<SyntacticFunctionSymbol> free) {
        return DependencyPairs.create(prog.getRules(), prog.getSignature(), tuple, onlyFree, free);
    }

    /**
     * Computes the dependency pairs using Tuple Symbols for all defined function symbols.
     * @param programRules The set of rules to determine the dependency pairs for.
     * @param sig The set of names that cannot be used for the new symbols.
     * @return The dependency pairs for the given set of rules.
     */
    public static DependencyPairs create(Collection<Rule> programRules, List sig) {
    return DependencyPairs.create(programRules, sig, true, false, null);
    }

    /**
     * Computes the dependency pairs.
     * @param programRules The set of rules to determine the dependency pairs for.
     * @param sig The set of names that cannot be used for the new symbols.
     * @param tuple Specifies whether to use Tuple Symbols.
     * @param onlyFree Specifies whether only free function symbols get TupleSymbols.
     * @param free Specifies the free function symbols.
     * @return The dependency pairs for the given set of rules.
     */
    public static DependencyPairs create(Collection<Rule> programRules, List<String> sig, boolean tuple, boolean onlyFree, Set<SyntacticFunctionSymbol> free) {
        boolean rhssub = (free != null);  // true iff subterms of rhss are to be considered even if they also occur on the lhs (Dershowitz)
        DependencyPairs dps = new DependencyPairs();
        FreshNameGenerator fng = new FreshNameGenerator(sig, FreshNameGenerator.DEPENDENCY_PAIRS);
        // Gehe alle Programmregeln durch und bestimme fuer jede Programmregel alle
        // zugehoerigen Dependencypairs
        Iterator j = programRules.iterator();
        while (j.hasNext()) {
            Rule rule = (Rule) j.next();
            AlgebraTerm left = rule.getLeft();
            // Hier wird der Term des linken Dependencypairs konstruiert
        AlgebraTerm leftDP = left;
        if(tuple && (!onlyFree || free.contains(left.getSymbol()))) {
                leftDP = ConstructorApp.create(DependencyPairs.getTupleSymbol(fng, left), left.getArguments());
        }
            Set<AlgebraTerm> leftSubs = null;
            if (!rhssub) {
                leftSubs = new HashSet<AlgebraTerm>(left.getAllProperSubterms());
            }
            // Hier werden die rechten Seiten aller Dependencypairs bestimmt und zusammen
            // mit der oben schon bestimmten linken Seite der Liste der bereits
            // berechneten Dependency Pairs hinzugefuegt.
            Iterator i = rule.getRight().getDefFunctionSubterms().iterator();
            while (i.hasNext()) {
                AlgebraTerm term = (AlgebraTerm)i.next();
        AlgebraTerm rightDP = term;
                if (!rhssub && leftSubs.contains(term)) {
                    continue;
                }
        if(tuple  && (!onlyFree || free.contains(term.getSymbol()))) {
                    rightDP = ConstructorApp.create(DependencyPairs.getTupleSymbol(fng, term), term.getArguments());
        }
                dps.add(Rule.create(leftDP, rightDP));
            }
        }
        return dps;
    }

    /**
     * Gives a representation of the Dependency Pairs in plain text,
     * suitable to be used in proof output
     *
     * @return a <code>String</code> of plain text representing this
     * object
     */
    @Override
    public String toPLAIN() {

        StringBuffer result = new StringBuffer();
        Iterator i = this.iterator();
        while (i.hasNext()) {
            result.append("   " + ((Rule) i.next()).toPLAIN());
            if (i.hasNext()) {
                result.append("\n");
            }
        }
        return result.toString();

    }

    @Override
    public String toHTML() {
        StringBuffer result = new StringBuffer();
        Iterator i = this.iterator();
        while (i.hasNext()) {
            result.append(((Rule)i.next()).toHTML());
            if (i.hasNext()) {
                result.append("<BR>");
            }
        }
        return result.toString();
    }

    @Override
    public String toLaTeX() {
        StringBuffer result = new StringBuffer();
        result.append("\\begin{longtable}{rcl}\n");
        Iterator i = this.iterator();
        while (i.hasNext()) {
            result.append(((Rule)i.next()).toLaTeX());
            if (i.hasNext()) {
                result.append("\\\\ \n");
            }
        }
        result.append("\n\\end{longtable}\n");
        return result.toString();
    }

}
