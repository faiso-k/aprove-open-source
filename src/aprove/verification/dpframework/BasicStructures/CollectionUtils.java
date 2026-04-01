package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.Globals;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;

/**
 * Created on 12.04.2005.
 * Just a collection of static methods to deal with collections of something.
 * @author thiemann
 * @version $Id$
 */
public abstract class CollectionUtils {

    /**
     * get the set of root symbols of the given collection
     * the resulting set may be modified!
     */
    public static Set<FunctionSymbol> getRootSymbols(final Iterable<? extends HasRootSymbol> rs) {
        final Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        for (final HasRootSymbol r : rs) {
            fs.add(r.getRootSymbol());
        }
        return fs;
    }

    /**
     * get the set of function symbols of the given collection
     * the resulting set may be modified!
     */
    public static Set<FunctionSymbol> getFunctionSymbols(final Iterable<? extends HasFunctionSymbols> fs_it) {
        final Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        for (final HasFunctionSymbols hfs : fs_it) {
            fs.addAll(hfs.getFunctionSymbols());
        }
        return fs;
    }

    /**
     * get the set of variables of the given collection
     * the resulting set may be modified!
     */
    public static Set<? extends Variable> getVariables(Iterable<? extends HasVariables> var_it) {
        final Set<Variable> vars = new LinkedHashSet<Variable>();
        for (HasVariables vs : var_it) {
            vars.addAll(vs.getVariables());
        }
        return vars;
    }

    /**
     * Returns the set of all terms,
     * the set may safely be modified
     * @return
     */
    public static Set<TRSTerm> getTerms(final Iterable<? extends HasTRSTerms> terms_it) {
        final Set<TRSTerm> all_terms = new LinkedHashSet<TRSTerm>();
        for (final HasTRSTerms terms : terms_it) {
            all_terms.addAll(terms.getTerms());
        }
        return all_terms;
    }


    public static Set<TRSFunctionApplication> getLeftHandSides(final Iterable<? extends HasLHS> rule_it) {
        final Set<TRSFunctionApplication> lhss = new LinkedHashSet<TRSFunctionApplication>();
        for (final HasLHS rule : rule_it) {
            lhss.add(rule.getLeft());
        }
        return lhss;
    }

    /**
     * checks whether the lefthandsides of the given collection are overlapping
     */
    public static boolean isOverlapping(final Iterable<? extends HasLHS> rule_it){
        // first get all those left-hand sides that could be involved in
        // an overlap (some left-hand sides may have multiple occurrences,
        // then we will immediately have an overlap)
        final List<TRSFunctionApplication> rootTerms = new ArrayList<TRSFunctionApplication>();
        for (final HasLHS rule : rule_it) {
            TRSFunctionApplication rootNormalised = (TRSFunctionApplication)
                    rule.getLeft().renumberVariables(TRSTerm.SECOND_STANDARD_PREFIX);
            rootTerms.add(rootNormalised);
        }
        // Overlaps can happen at the root of a left-hand side (overlays) ...
        final int length = rootTerms.size();
        for (int i = length - 1; i >= 0; --i) {
            final TRSFunctionApplication lhs1 = rootTerms.get(i);
            // start at i - 1 to avoid double-counting and self-overlaps
            for (int j = i - 1; j >= 0; --j) {
                final TRSFunctionApplication lhs2 = rootTerms.get(j);
                if (lhs1.unifiesVarDisjoint(lhs2)) { // implicit var renaming
                    // also catches duplicate left-hand sides
                    return true;
                }
            }
        }

        // ... or at a proper subterm of a left-hand side:
        // (1) collect these subterms (optimization: without duplicates)
        final Set<TRSTerm> lhssProperSubterms = new LinkedHashSet<TRSTerm>();
        for (final TRSFunctionApplication lhs : rootTerms){
            for (final TRSTerm lhsArg : lhs.getArguments()) {
                for (TRSTerm lhsArgSubterm : lhsArg.getNonVariableSubTerms()) {
                    lhssProperSubterms.add(lhsArgSubterm.renumberVariables(TRSTerm.THIRD_STANDARD_PREFIX));
                }
            }
        }
        // (2) check each root against each (variable-renamed) subterm
        for (final TRSFunctionApplication lhs : rootTerms){
            for (final TRSTerm subterm : lhssProperSubterms){
                if (lhs.unifies(subterm)) { // variables renamed manually
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * checks whether the lefthandsides of the given collection are leftlinear
     */
    public static boolean isLeftLinear(final Iterable<? extends HasLHS> rule_it){
        final Set<TRSFunctionApplication> lhss = CollectionUtils.getLeftHandSides(rule_it);

        for(final TRSFunctionApplication lhs : lhss){
            if(!lhs.isLinear()){
                return false;
            }
        }
        return true;
    }

    /**
     * checks whether the righthandsides of the given collection are rightlinear
     */
    public static boolean isRightLinear(final Iterable<Rule> rules){
        for(final Rule rule : rules){
            if(!rule.getRight().isLinear()){
                return false;
            }
        }
        return true;
    }

    public static void addChildren(final Collection<? extends XMLObligationExportable> children, final Element e, final Document doc, final XMLMetaData xmlMetaData) {
        for (final XMLObligationExportable child : children) {
            e.appendChild(child.toDOM(doc, xmlMetaData));
        }
    }

    public static void addCPFChildren(
        final Collection<? extends CPFAdditional> children,
        final Element e,
        final Document doc,
        final XMLMetaData xmlMetaData)
    {
        for (final CPFAdditional child : children) {
            final Element arg = CPFTag.ARG.createElement(doc);
            arg.appendChild(child.toCPF(doc, xmlMetaData));
            e.appendChild(arg);
        }
    }

    public static <T extends XMLProofExportable> void addChildren(final T[] children, final Element e, final Document doc, final XMLMetaData storage) {
        for (final XMLProofExportable child : children) {
            e.appendChild(child.toDOM(doc, storage));
        }
    }

    /**
     * @param hasNames
     * @return a set of the names in hasNames; this set may be modified
     */
    public static Set<String> getNames(final Iterable<? extends HasName> hasNames) {
        final Set<String> names = new LinkedHashSet<String>();
        for (final HasName hasName : hasNames) {
            names.add(hasName.getName());
        }
        return names;
    }

    /**
     * Note that the result of this method is subtly different from
     * the set of head symbols of the DP problem (pRules, rRules).
     *
     * @return if pRules only contains non-collapsing rules s -> t and
     *  if the set of root symbols of s and t is disjoint with the sets
     *  of function symbols at the non-root positions of pRules and of
     *  function symbols of rRules at arbitrary positions: the root symbols
     *  of these s and t; null otherwise. The resulting set may be modified.
     */
    public static Set<FunctionSymbol> getTupleSymbols(final Iterable<? extends GeneralizedRule> pRules,
            final Iterable<? extends GeneralizedRule> rRules) {

        // first determine possible result ...
        final Set<FunctionSymbol> result = new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> forbidden = new LinkedHashSet<FunctionSymbol>();
        for (final GeneralizedRule pRule : pRules) {
            final TRSFunctionApplication l = pRule.getLeft();
            result.add(l.getRootSymbol());
            forbidden.addAll(l.getNonRootFunctionSymbols());

            final TRSTerm rTerm = pRule.getRight();
            if (rTerm.isVariable()) {
                return null;
            }
            else { // pRule non-collapsing
                final TRSFunctionApplication r = (TRSFunctionApplication) rTerm;
                result.add(r.getRootSymbol());
                forbidden.addAll(r.getNonRootFunctionSymbols());
            }
        }

        forbidden.addAll(CollectionUtils.getFunctionSymbols(rRules));

        // ... then check whether the "tuple symbol condition" is fulfilled
        if (java.util.Collections.disjoint(result, forbidden)) {
            // the input has the desired shape, so the roots of the P-terms
            // really are "tuple symbols" :)
            return result;
        }
        return null;
    }

    /**
     * Returns the maximum arity of a number of objects with arities.
     *
     * @param hasArities must not contain null
     * @return the maximum arity of the objects obtained by iteration over
     *  hasArities; 0 if this iteration does not provide any objects
     */
    public static int getMaxArity(final Iterable<? extends HasArity> hasArities) {
        int result = 0;
        for (HasArity hasArity : hasArities) {
            int arity = hasArity.getArity();
            if (arity > result) {
                result = arity;
            }
        }
        return result;
    }

    /**
     * Returns whether the given collection of rules has at least one
     * non-trivial innermost critical overlay. (A critical overlay, aka a
     * critical pair at the root position, is _innermost_ if all strict
     * subterms of the term at the origin of the critical peak are in
     * normal form wrt the rewrite relation induced by the collection of
     * rules. It is non-trivial if both terms of the pair are different.)
     *
     * If the method returns false, the rules are innermost confluent
     * [PhD thesis Bernhard Gramlich, Theorem 3.5.6] and parallel-innermost
     * confluent.
     *
     * @param rules
     * @return whether the given collection of rules has at least one
     *  non-trivial innermost critical overlay
     * @throws NullPointerException if rules is or contains null
     */
    public static boolean hasNonTrivialInnermostCriticalOverlays(Collection<? extends Rule> rules) {
        int n = rules.size();
        Rule[] firstRules = new Rule[n];
        Rule[] secondRules = new Rule[n];
        Iterator<? extends Rule> ruleIter = rules.iterator();
        // get variable-disjoint occurrences of the rules
        for (int i = 0; i < n; ++i) {
            Rule rule = ruleIter.next();
            firstRules[i] = rule.getWithRenumberedVariables(TRSTerm.SECOND_STANDARD_PREFIX);
            secondRules[i] = rule.getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
        }
        if (Globals.useAssertions) {
            assert ! ruleIter.hasNext();
        }

        // handy for checking whether a term's arguments are in normal form
        QTermSet q = new QTermSet(getLeftHandSides(rules));
        for (int i = 0; i < n; ++i) {
            TRSTerm firstLHS = firstRules[i].getLeft();
            TRSTerm firstRHS = firstRules[i].getRight();
            inner : for (int j = 0; j < i; ++j) {
                TRSTerm secondLHS = secondRules[j].getLeft();
                TRSTerm secondRHS = secondRules[j].getRight();
                TRSSubstitution mgu = new Unification(firstLHS, secondLHS).getMgu();
                if (mgu == null) {
                    // not a _critical overlay_ at all
                    continue inner;
                }
                TRSTerm instance = firstLHS.applySubstitution(mgu);
                if (q.canBeRewrittenBelowRoot(instance)) {
                    // not an _innermost_ critical overlay
                    continue inner;
                }
                TRSTerm overlayLHS = firstRHS.applySubstitution(mgu);
                TRSTerm overlayRHS = secondRHS.applySubstitution(mgu);
                if (! overlayLHS.equals(overlayRHS)) {
                    // found an innermost critical overlay which is _non-trivial_
                    return true;
                }
            }
        }
        // nothing found? then the answer must be false
        return false;
    }
}
