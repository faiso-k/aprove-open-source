/*
 * Created on 30.10.2005
 */
package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.Globals.AproveVersion;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * A generalized rule is a pair of terms
 * where the lhs may be no variable
 * but there is no restriction on the set of variables of the rhs
 * (compare to standard rewrite rule in Rule.java)
 *
 * @author matraf
 */
public class GeneralizedRule extends RuleSchema
implements
    Immutable,
    HasTermPair,
    HasRuleForm
{

    /*
     * real values, note that the lhs is already defined in RuleSchema
     */
    protected final TRSTerm r;


    /*
     * computed values
     */
    protected final TRSFunctionApplication stdL;
    protected final TRSTerm stdR;

    protected int hashCode;

    private static boolean checkProperLandR(TRSFunctionApplication l, TRSTerm r) {
        return l != null
        && r != null
        ;
    }

    private static boolean checkProperStd(
        TRSFunctionApplication l,
        TRSFunctionApplication stdL,
        TRSTerm r,
        TRSTerm stdR
    ) {
        if (stdL == null || stdR == null) {
            return false;
        }
        final Map<TRSVariable, TRSVariable> map = new HashMap<TRSVariable, TRSVariable>();
        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLAndInt =
            l.renumberVariables(map, TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
        if (!stdLAndInt.x.equals(stdL)) {
            return false;
        }
        final ImmutablePair<? extends TRSTerm, Integer> stdRAndInt =
            r.renumberVariables(map, TRSTerm.STANDARD_PREFIX, stdLAndInt.y);
        if (!stdRAndInt.x.equals(stdR)) {
            System.err.println(
                l + " -> " + r + " --- >>> " + stdLAndInt.x + " -> "+ stdRAndInt.x  + " -- >> " + stdR + " / " + map
            );
        }
        return stdRAndInt.x.equals(stdR);
    }


    /**
     * creates a new generalized rule.
     * Restrictions:
     *   neither l nor r may be null
     * @param l - a term
     * @param r - a term
     */
    protected GeneralizedRule(TRSFunctionApplication l, TRSTerm r, TRSFunctionApplication stdL, TRSTerm stdR) {
        this.l = l;
        this.r = r;
        if (Globals.useAssertions) {
            final boolean res = GeneralizedRule.checkProperLandR(l, r);
            assert (res);
            assert((stdL == null && stdR == null) || (stdL != null && stdR != null));
        }
        if (stdL == null) {
            final Map<TRSVariable, TRSVariable> map = new HashMap<TRSVariable, TRSVariable>();
            final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLAndInt =
                l.renumberVariables(map, TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
            final ImmutablePair<? extends TRSTerm, Integer> stdRAndInt =
                r.renumberVariables(map, TRSTerm.STANDARD_PREFIX, stdLAndInt.y);
            stdL = stdLAndInt.x;
            stdR = stdRAndInt.x;
        } else {
            // don't trust the user
            if (Globals.useAssertions) {
                final boolean res = GeneralizedRule.checkProperStd(this.l, stdL, this.r, stdR);
                assert (res);
            }
        }
        this.stdL = stdL;
        this.stdR = stdR;
        this.hashCode = 490321*stdL.hashCode() + 12812*stdR.hashCode() + 312038193;
    }


    /**
     * creates a new generalized rule
     * @param l
     * @param r
     */
    public static GeneralizedRule create(TRSFunctionApplication l, TRSTerm r) {
        return new GeneralizedRule(l, r, null, null);
    }

    /**
     * creates a new generalized rule
     * @param l
     * @param r
     */
    public static GeneralizedRule create(
        TRSFunctionApplication l,
        TRSTerm r,
        TRSFunctionApplication lStd,
        TRSTerm rStd
    ) {
        return new GeneralizedRule(l, r, lStd, rStd);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    /**
     * Equality is defined modulo variable renaming.
     *
     * In the impl. this is done using a standard representation of a rule
     */
    /*
     * if you remove the final and define some other kind
     * of equality for the children class, please
     * make sure that compareTo is also updated accordingly!!
     */
    public final boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof GeneralizedRule) {
            final GeneralizedRule rule = (GeneralizedRule)other;
            return this.hashCode == rule.hashCode && this.stdL.equals(rule.stdL) && this.stdR.equals(rule.stdR);
        }
        return false;
    }

    @Override
    public final int compareTo(RuleSchema other) {
    	if (!(other instanceof GeneralizedRule)) {
    		return 1;
    	} 
    	GeneralizedRule otherGen = (GeneralizedRule) other;
    	int compare = this.stdL.compareTo(otherGen.stdL);
        if (compare == 0) {
            compare = this.stdR.compareTo(otherGen.stdR);
        }
        return compare;
    }

    /**
     * returns the lhs
     */
    @Override
    public TRSFunctionApplication getLeft() {
        return this.l;
    }

    /**
     * returns the rhs.
     */
    @Override
    public TRSTerm getRight() {
        return this.r;
    }


    /**
     * returns the set of terms occurring in this rule,
     * i.e. {l,r}
     */
    @Override
    public Set<TRSTerm> getTerms() {
        final Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
        res.add(this.l);
        res.add(this.r);
        return res;
    }

    /**
     * returns the set of variables occurring in this rule
     */
    @Override
    public Set<TRSVariable> getVariables() {
        final Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>(this.l.getVariables());
        vars.addAll(this.r.getVariables());
        return vars;
    }

    /**
     * returns the set of variables occurring on the rhs but not on the lhs.
     */
    public Set<TRSVariable> getUnboundedVariables() {
        final Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>(this.r.getVariables());
        vars.removeAll(this.l.getVariables());
        return vars;
    }

    /**
     * returns the set of functionSymbols occurring in this rule.
     * the resulting set may be modified
     */
    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        final Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        this.l.collectFunctionSymbols(fs);
        this.r.collectFunctionSymbols(fs);
        return fs;
    }

    /**
     * returns the root symbol of this rule,
     * i.e. the root symbol of the lhs.
     */
    @Override
    public FunctionSymbol getRootSymbol() {
        return this.getLeft().getRootSymbol();
    }

    /**
     * renames the variables with given prefix and
     * numbers starting from STANDARD_NUMBER.
     * E.g., for rule = f(x,y,x1,y) -> f(y,x,x,a)
     *           prefix = x
     *           STANDARD_NUMBER = 0
     *    we obtain  f(x0,x1,x2,x1) -> f(x1,x0,x0,a).
     *
     * The standard representation of a rule is
     * rule.getWithRenumberedVariables(STANDARD_PREFIX);
     * @param prefix
     * @return
     */
    public GeneralizedRule getWithRenumberedVariables(final String prefix) {
        final Map<TRSVariable, TRSVariable> map = new HashMap<TRSVariable, TRSVariable>();
        final ImmutablePair<? extends TRSFunctionApplication, Integer> numberedLAndInt =
            this.getLeft().renumberVariables(map, prefix, TRSTerm.STANDARD_NUMBER);
        final ImmutablePair<? extends TRSTerm, Integer> numberedRAndInt =
            this.r.renumberVariables(map, prefix, numberedLAndInt.y);
        return new GeneralizedRule(numberedLAndInt.x, numberedRAndInt.x, this.stdL, this.stdR);
    }

    /**
     * returns the lhs in standardRepresentation.
     * (constant time)
     */
    public TRSFunctionApplication getLhsInStandardRepresentation() {
        return this.stdL;
    }

    /**
     * returns the rhs in standardRepresentation.
     * (constant time)
     */
    public TRSTerm getRhsInStandardRepresentation() {
        return this.stdR;
    }

    /**
     * returns a the standard representation of this
     * rule where l = stdL and r = stdR.
     * (constant time)
     * @see getWithRenumberedVariables
     */
    public GeneralizedRule getStandardRepresentation() {
        // should be equivalent to getWithRenumberedVariables(STANDARD_PREFIX);
        return new GeneralizedRule(this.stdL, this.stdR, this.stdL, this.stdR);
    }

    @Override
    public String export(Export_Util eu) {
        java.util.Collection<TRSVariable> freeVariables;
        if (Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION) {
            freeVariables = this.r.getVariables();
            freeVariables.removeAll(this.l.getVariables());
        } else {
            freeVariables = java.util.Collections.<TRSVariable> emptySet();
        }
        return this.getLeft().export(eu) + " " + eu.rightarrow() + " "
            + this.getRight().export(eu, freeVariables);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Element toDOM(Document doc, XMLMetaData xmlMetaData) {
        final Element e = XMLTag.RULE.createElement(doc);
        e.appendChild(this.l.toDOM(doc, xmlMetaData));
        e.appendChild(this.r.toDOM(doc, xmlMetaData));
        return e;
    }

    @Override
    public Element toCPF(Document doc, XMLMetaData xmlMetaData) {
        final Element e = CPFTag.RULE.createElement(doc);
        final Element lhs = CPFTag.LHS.createElement(doc);
        lhs.appendChild(this.l.toCPF(doc, xmlMetaData));
        final Element rhs = CPFTag.RHS.createElement(doc);
        rhs.appendChild(this.r.toCPF(doc, xmlMetaData));
        e.appendChild(lhs);
        e.appendChild(rhs);
        return e;
    }

    /**
     * this method takes  a set of rules and iterates over
     * all critical pairs. Non-root overlaps will be returned before
     * root overlaps.
     * @param rules
     */
    public static AbortableIterator<ImmutableTriple<TRSTerm, TRSTerm, Boolean>> getCriticalPairs(
        Set<? extends GeneralizedRule> rules
    ) {
        return new CritPairIterator(rules);
    }

    /**
     * helper classes
     */
    protected static class CritPairIterator implements AbortableIterator<ImmutableTriple<TRSTerm, TRSTerm, Boolean>> {

        private static final int MASK = 0x20;

        private final GeneralizedRule[] rootRules;
        private int posRoot;
        private int posOther;
        private final int n;
        private final int n_minus_1;
        private boolean nextValid;
        private ImmutableTriple<TRSTerm, TRSTerm, Boolean> nextCritPair;
        private Iterator<Pair<Position, TRSFunctionApplication>> currentOtherPositions;
        private int count = 0;

        /**
         * a critPairIterator takes a set of rules and iterates over
         * all critical pairs. Non-root overlaps will be returned before
         * root overlaps.
         * @param rules
         */
        private CritPairIterator(Set<? extends GeneralizedRule> rules) {
            this.n = rules.size();
            this.n_minus_1 = this.n - 1;
            this.rootRules = new GeneralizedRule[this.n];
            int i = 0;

            for (GeneralizedRule rule : rules) {
                this.rootRules[i] = rule.getWithRenumberedVariables(TRSTerm.SECOND_STANDARD_PREFIX);
                i++;
            }

            if (this.n == 0) {
                this.nextValid = true;
            } else {
                this.nextValid = false;
                this.currentOtherPositions =
                    this.rootRules[0].getLeft().getNonRootNonVariablePositionsWithSubTerms().iterator();
            }
            this.posRoot = 0;
            this.posOther = 0;
            this.nextCritPair = null;
        }

        private void computeNext(Abortion aborter) throws AbortionException {
            if (this.currentOtherPositions != null) {
                while (this.posRoot != this.n) {
                    final GeneralizedRule rootRule = this.rootRules[this.posRoot];
                    final TRSTerm left = rootRule.getLhsInStandardRepresentation();
                    final TRSTerm right = rootRule.getRhsInStandardRepresentation();
                    while (this.posOther != this.n) {
                        final GeneralizedRule otherRule = this.rootRules[this.posOther];
                        final TRSTerm otherLeft = otherRule.getLeft();
                        final TRSTerm otherRight = otherRule.getRight();
                        if (this.currentOtherPositions == null) {
                            this.currentOtherPositions =
                                otherLeft.getNonRootNonVariablePositionsWithSubTerms().iterator();
                        }
                        while (this.currentOtherPositions.hasNext()) {
                            this.count++;
                            if ((this.count & CritPairIterator.MASK) != 0) {
                                this.count = 0;
                                aborter.checkAbortion();
                            }
                            final Pair<Position, TRSFunctionApplication> posAndSubLeft =
                                this.currentOtherPositions.next();
                            final TRSFunctionApplication subLeft = posAndSubLeft.y;
                            final TRSSubstitution sigma = left.getMGU(subLeft);
                            if (sigma != null) {
                                final TRSTerm otherRightSigma = otherRight.applySubstitution(sigma);
                                final TRSTerm otherLeftRightAtP_sigma =
                                    otherLeft.replaceAt(posAndSubLeft.x, right).applySubstitution(sigma);
                                this.nextCritPair =
                                    new ImmutableTriple<TRSTerm, TRSTerm, Boolean>(
                                        otherRightSigma,
                                        otherLeftRightAtP_sigma,
                                        false
                                    );
                                this.nextValid = true;
                                return;
                            }
                        }
                        this.posOther++;
                        this.currentOtherPositions = null;
                    }
                    this.posRoot ++;
                    this.posOther = 0;
                }
                this.posRoot = 0;
                this.posOther = 1;
            }
            while (this.posRoot != this.n_minus_1) {
                final GeneralizedRule rootRule = this.rootRules[this.posRoot];
                final TRSTerm left = rootRule.getLhsInStandardRepresentation();
                final TRSTerm right = rootRule.getRhsInStandardRepresentation();
                while (this.posOther != this.n) {
                    final GeneralizedRule otherRule = this.rootRules[this.posOther];
                    final TRSTerm otherLeft = otherRule.getLeft();
                    this.posOther++;
                    final TRSSubstitution sigma = left.getMGU(otherLeft);
                    if (sigma != null) {
                        final TRSTerm rightSigma = right.applySubstitution(sigma);
                        final TRSTerm otherRightSigma = otherRule.getRight().applySubstitution(sigma);
                        this.nextCritPair =
                            new ImmutableTriple<TRSTerm, TRSTerm, Boolean>(rightSigma, otherRightSigma, true);
                        this.nextValid = true;
                        return;
                    }
                }
                this.posRoot++;
                this.posOther = this.posRoot+1;
            }
            this.nextCritPair = null;
            this.nextValid = true;
        }

        @Override
        public boolean hasNext(Abortion aborter) throws AbortionException {
            if (!this.nextValid) {
                this.computeNext(aborter);
            }
            return this.nextCritPair != null;
        }

        @Override
        public ImmutableTriple<TRSTerm, TRSTerm, Boolean> next(Abortion aborter) throws AbortionException {
            if (this.hasNext(aborter)) {
                this.nextValid = false;
                return this.nextCritPair;
            } else {
                throw new NoSuchElementException();
            }
        }

    }
}
