package aprove.verification.dpframework.BasicStructures;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;
import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * A coupled positional dependency tuple is a rule of the form (l^#, l) -> (C, r)
 * where C is a set of dependency terms C = dp(r).
 * 
 * TODO: any of this needed:
 * We have the standard rule
 * restrictions, namely that the lhs is not a variable and that the variables of
 * the rhs is a subset of the variables on the lhs (i.e., V(Aj) subset V(l) and
 * V(rj) subset V(l)) for all 1 <= j <= k.
 *
 * @author Grigory Vartanyan
 * @version $Id$
 */
public class CoupledPosDepTuple extends RuleSchema implements
        Immutable,
//        HasPairLHS,  // TODO: stole from Kassing's interface and removed
//        HasProbCoupledPosDepRHS,  // TODO: stole from Kassing's interface and removed
        HasFunctionSymbols  // TODO: stole from Kassing's interface
    {

    // ================================================================================
    // Properties
    // ================================================================================

    /** real lhs */
    private final Pair<TRSFunctionApplication, TRSFunctionApplication> l;

    /** real rhs */
    private final Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> r;

    /** lhs with standardised variable names*/
    private final Pair<TRSFunctionApplication, TRSFunctionApplication> stdL;

    /** rhs with standardised variable names*/
    private final Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> stdR;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    /**
     * Create a new Rule. l and r must not be null and stdL and stdR are either both
     * null or both not null.
     * 
     * @param l    lhs
     * @param r    rhs
     * @param stdL standardised lhs
     * @param stdR standardised rhs
     */
    protected CoupledPosDepTuple(
        Pair<TRSFunctionApplication, TRSFunctionApplication> l,
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> r,
        Pair<TRSFunctionApplication, TRSFunctionApplication> stdL,
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> stdR
    ) {
        this.l = l;
        this.r = r;

        if (Globals.useAssertions) {
            // TODO: is there a reason Kassing didn't do these like this?
            assert CoupledPosDepTuple.checkProperLandR(l, r);
            assert (stdL == null) == (stdR == null);
        }

        if (stdL == null) {
            Pair<
                Pair<TRSFunctionApplication, TRSFunctionApplication>,
                Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>
            > stdLR = makeStdLR(l, r);

            this.stdL = stdLR.x;
            this.stdR = stdLR.y;
        } else {
            // don't trust the user
            if (Globals.useAssertions) {
                assert CoupledPosDepTuple.checkProperStd(this.l, stdL, this.r, stdR);
            }
            this.stdL = stdL;
            this.stdR = stdR;
        }

        this.hashCode = 64324 * this.stdL.hashCode() + 1337 * this.stdR.hashCode() + 4835754;
    }

    /**
     * Create a new Rule.
     * 
     * @param l lhs
     * @param r rhs
     */
    public static CoupledPosDepTuple create(
        Pair<TRSFunctionApplication, TRSFunctionApplication> l,
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> r
    ) {
        return new CoupledPosDepTuple(l, r, null, null);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    /**
     * returns the standard representation of this rule where l = stdL and r = stdR.
     * (constant time)
     * 
     * @see getWithRenumberedVariables
     * @return the standard representation of this rule
     */
    public CoupledPosDepTuple getStandardRepresentation() {
        // should be equivalent to getWithRenumberedVariables(STANDARD_PREFIX);
        return new CoupledPosDepTuple(this.stdL, this.stdR, this.stdL, this.stdR);
    }

    /**
     * @return the pair of the lhs (l^#, l)
     */
    public Pair<TRSFunctionApplication, TRSFunctionApplication> getLeftPair() {
        return l;
    }

    /**
     * Returns the second component in the lhs, i.e., it returns 
     * root((l^#,l) -> ...) = l.
     * 
     * @return the second component in the lhs
     */
    @Override
    public TRSFunctionApplication getLeft() {
        return l.y;
    }

    /**
     * Returns the first component in the lhs, i.e., it returns 
     * root((l^#,l) -> ...) = l^#.
     * 
     * @return the first component in the lhs
     */
    public TRSFunctionApplication getTupleLeft() {
        return l.x;
    }

    /**
     * Returns the canonicalized second component in the lhs, i.e., it returns
     * root((l^#,l) -> ...) = l (with renamed variables).
     * 
     * @return the canonicalized second component in the lhs
     */
    @Override
    public TRSFunctionApplication getLhsInStandardRepresentation() {
        return stdL.y;
    }

    /**
     * Returns the canonicalized first component in the lhs, i.e., it returns
     * root((l^#,l) -> ...) = l^# (with renamed variables).
     * 
     * @return the canonicalized first component in the lhs
     */
    public TRSFunctionApplication getTupleLhsInStandardRepresentation() {
        return stdL.x;
    }

    /**
     * @return the rhs
     */
    public Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> getRightPair() {
        return r;
    }

    /**
     * @return the set of rhs DTs
     */
    public Set<Pair<TRSFunctionApplication, Position>> getC() {
        return r.x;
    }

    /**
     * Returns the canonicalized rhs.
     * 
     * @return the canonicalized rhs
     */
    @Override
    public Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> getRhsInStandardRepresentation() {
        return stdR;
    }

    /**
     * Quick check, whether everything is not null.
     */
    private static boolean checkProperLandR(
        Pair<TRSFunctionApplication, TRSFunctionApplication> l,
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> r
    ) {
        return l != null && l.x != null && l.y != null
            && r != null && r.x != null && r.y != null;
        // TODO: Do we have (or want) to check everything?
        // TODO: Should I check the values inside C?
    }

    /**
     * returns the set of terms occurring in this rule, i.e. l and the support of r.
     * 
     * @return the set of terms occurring in this rule
     */
    @Override
    public Set<TRSTerm> getTerms() {
        final Set<TRSTerm> res = new LinkedHashSet<>();
        res.add(l.x);
        res.add(l.y);
        for (Pair<TRSFunctionApplication, Position> pdt : r.x) {
            res.add(pdt.getKey());
        }
        res.add(r.y);
        return res;
    }

    /**
     * returns the set of function symbols occurring in this rule, i.e. l and the
     * support of r.
     * 
     * @return the set of function symbols occurring in this rule
     */
    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        final Set<FunctionSymbol> res = new LinkedHashSet<>();
        res.addAll(l.x.getFunctionSymbols());
        res.addAll(l.y.getFunctionSymbols());
        for (Pair<TRSFunctionApplication, Position> pdt : r.x) {
            res.addAll(pdt.x.getFunctionSymbols());
        }
        res.addAll(r.y.getFunctionSymbols());
        return res;
    }

    /**
     * returns the set of variables occurring in this rule, i.e. l and the support
     * of r.
     * 
     * @return the set of variables occurring in this rule
     */
    @Override
    public Set<TRSVariable> getVariables() {
        final Set<TRSVariable> res = new LinkedHashSet<>();
        res.addAll(l.x.getVariables());
        res.addAll(l.y.getVariables());
        for (Pair<TRSFunctionApplication, Position> pdt : r.x) {
            res.addAll(pdt.x.getVariables());
        }
        res.addAll(r.y.getVariables());
        return res;
    }

    /**
     * returns the set of tuple terms occurring in the rhs of this rule, i.e. the
     * support of r.
     * 
     * @return the set of tuple terms occurring in the rhs of this rule
     */
    public Set<TRSFunctionApplication> getAllTupleTermsInRHS() {
        final Set<TRSFunctionApplication> res = new LinkedHashSet<>();
        for (Pair<TRSFunctionApplication, Position> pdt : this.getC()) {
            res.add(pdt.x);
        }
        return res;
    }

    // TODO: do I need this?
    /**
     * Removes every pair that has the term t as its first argument from the RHS.
     * 
     * @param t the term that should be removed.
     * @return a new CoupledPosDepTuple that results from this one if we remove
     *         every occurrence of t from the RHS.
     */
    /*
    public CoupledPosDepTuple removeTupleTermFromRHS(TRSFunctionApplication t) {
        // Create new RHS
        final HashMultiSet<Pair<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>, Fraction>> newProbabilityMap = new HashMultiSet<>();
        for (Entry<?, Integer> entry : stdR.getProbabilityMapping().entrySet()) {
            Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledSetTermElement = ((Pair<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>, Fraction>) entry
                    .getKey()).getKey();
            Fraction prob = ((Pair<TRSTerm, Fraction>) entry.getKey()).getValue();
            Integer amount = entry.getValue();

            // Remove every occurrence of t from the RHS
            Set<Pair<TRSFunctionApplication, Position>> stdSet = new HashSet<Pair<TRSFunctionApplication, Position>>();
            for (Pair<TRSFunctionApplication, Position> termPositionPair : coupledSetTermElement.x) {
                if (!termPositionPair.x.equals(t)) {
                    stdSet.add(new Pair<TRSFunctionApplication, Position>(termPositionPair.x, termPositionPair.y));
                }
            }
            Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> stdCoupledSetTermElement = new Pair<>(
                    stdSet,
                    coupledSetTermElement.y);
            newProbabilityMap.put(
                    new Pair<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>, Fraction>(
                            stdCoupledSetTermElement, prob),
                    amount);
        }

        final Pair<TRSFunctionApplication, TRSFunctionApplication> resLHS = this.getLeftPair();
        final MultiDistribution<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>> resRHS = new MultiDistribution<>(
                newProbabilityMap);

        return CoupledPosDepTuple.create(resLHS, resRHS);
    } */

    @Override
    /**
     * Returns the root symbol of the second component in the lhs, i.e., it returns
     * root((l^#,l) -> ...) = root(l).
     * 
     * @return the root symbol of the second component in the lhs
     */
    public FunctionSymbol getRootSymbol() {
        return l.y.getRootSymbol();
    }

    /**
     * Returns the root symbol of the first component in the lhs, i.e., it returns
     * root((l^#,l) -> ...) = root(l^#).
     * 
     * @return the root symbol of the first component in the lhs
     */
    public FunctionSymbol getTupleRootSymbol() {
        return l.x.getRootSymbol();
    }

    // ================================================================================
    // canonicalization
    // ================================================================================

    /**
     * Compute the canonical representation of l and r by renumbering the variables.
     * Set these as stdL and stdR
     * 
     * @param l lhs
     * @param r rhs
     * @param prefix
     * @return Pair<stdLHS, stdRHS>
     */
    private static Pair<
        Pair<TRSFunctionApplication, TRSFunctionApplication>,
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>
    > standardise_vars(
        Pair<TRSFunctionApplication, TRSFunctionApplication> l,
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> r,
        String prefix
    ) {
        final Map<TRSVariable, TRSVariable> new_names = new HashMap<>();

        // Create stdLHS.x
        final ImmutablePair<? extends TRSFunctionApplication, Integer> res_lx = l.x
            .renumberVariables(new_names, prefix, TRSTerm.STANDARD_NUMBER);
        Integer next_free_num = res_lx.y;

        // Create stdLHS.y
        final ImmutablePair<? extends TRSFunctionApplication, Integer> res_ly = l.y
            .renumberVariables(new_names, prefix, next_free_num);
        next_free_num = res_ly.y;

        // Create stdRHS.y
        final ImmutablePair<? extends TRSTerm, Integer> res_ry = r.y
            .renumberVariables(new_names, prefix, next_free_num);
        next_free_num = res_ry.y;

        // Create stdRHS.x (build the set up)
        Set<Pair<TRSFunctionApplication, Position>> res_rx_set = new HashSet<>();
        for (Pair<TRSFunctionApplication, Position> pdt : r.x) {
            final ImmutablePair<? extends TRSFunctionApplication, Integer> res_rx = pdt.x
                    .renumberVariables(new_names, prefix, next_free_num);
            next_free_num = res_rx.y;
            res_rx_set.add(new Pair<TRSFunctionApplication, Position>(res_rx.x, pdt.y));
        }

        return new Pair<>(
            new Pair<>(res_lx.x, res_ly.x),
            new Pair<>(res_rx_set, res_ry.x)
        );
    }
    
    /**
     * Compute the canonical representation of l and r by renumbering the variables.
     * Set these as stdL and stdR
     * 
     * @param l lhs
     * @param r rhs
     * @return Pair<stdLHS, stdRHS>
     */
    private Pair<
        Pair<TRSFunctionApplication, TRSFunctionApplication>,
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>
    > makeStdLR(
        Pair<TRSFunctionApplication, TRSFunctionApplication> l,
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> r
    ) {
        return CoupledPosDepTuple.standardise_vars(l, r, TRSTerm.STANDARD_PREFIX);

//        final Map<TRSVariable, TRSVariable> new_names = new HashMap<>();
//
//        // Create stdLHS.x
//        final ImmutablePair<? extends TRSFunctionApplication, Integer> res_lx = l.x
//            .renumberVariables(new_names, TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
//        Integer next_free_num = res_lx.y;
//
//        // Create stdLHS.y
//        final ImmutablePair<? extends TRSFunctionApplication, Integer> res_ly = l.y
//            .renumberVariables(new_names, TRSTerm.STANDARD_PREFIX, next_free_num);
//        next_free_num = res_ly.y;
//
//        // Create stdRHS.y
//        final ImmutablePair<? extends TRSTerm, Integer> res_ry = r.y
//            .renumberVariables(new_names, TRSTerm.STANDARD_PREFIX, next_free_num);
//        next_free_num = res_ry.y;
//
//        // Create stdRHS.x (build the set up)
//        Set<Pair<TRSFunctionApplication, Position>> res_rx_set = new HashSet<>();
//        for (Pair<TRSFunctionApplication, Position> pdt : r.x) {
//            final ImmutablePair<? extends TRSFunctionApplication, Integer> res_rx = pdt.x
//                    .renumberVariables(new_names, TRSTerm.STANDARD_PREFIX, next_free_num);
//            next_free_num = res_rx.y;
//            res_rx_set.add(new Pair<TRSFunctionApplication, Position>(res_rx.x, pdt.y));
//        }
//
//        return new Pair<>(
//            new Pair<>(res_lx.x, res_ly.x),
//            new Pair<>(res_rx_set, res_ry.x)
//        );
    }

    /**
     * Check that stdL and stdR are correct canonicalized versions of l and r.
     * 
     * @param l    lhs
     * @param r    rhs
     * @param stdL canonicalized lhs that we want to check
     * @param stdR canonicalized rhs that we want to check
     */
    private static boolean checkProperStd(
        Pair<TRSFunctionApplication, TRSFunctionApplication> l,
        Pair<TRSFunctionApplication, TRSFunctionApplication> stdL,
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> r,
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> stdR
    ) {
        // TODO: Does not short circuit anymore... maybe split L and R up in the main method
        if (stdL == null || stdR == null) { return false; }

        var res = CoupledPosDepTuple.standardise_vars(l, r, TRSTerm.STANDARD_PREFIX);
        return res.x.equals(stdL) && res.y.equals(stdR);

//        final Map<TRSVariable, TRSVariable> map = new HashMap<>();
//
//        // Check stdLHS
//        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLOneAndInt = l.x.renumberVariables(map,
//                TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
//        Integer nextFreeNr = stdLOneAndInt.y;
//        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLTwoAndInt = l.y.renumberVariables(map,
//                TRSTerm.STANDARD_PREFIX, nextFreeNr);
//        nextFreeNr = stdLTwoAndInt.y;
//        Pair<TRSFunctionApplication, TRSFunctionApplication> resultStdLHS = new Pair<TRSFunctionApplication, TRSFunctionApplication>(
//                stdLOneAndInt.x,
//                stdLTwoAndInt.x);
//
//        if (!resultStdLHS.equals(stdL)) {
//            return false;
//        }
//
//        // Check stdRHS
//        final HashMultiSet<Pair<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>, Fraction>> stdProbabilityMap = new HashMultiSet<>();
//        for (Entry<?, Integer> entry : r.getProbabilityMapping().entrySet()) {
//            Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledSetTermElement = ((Pair<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>, Fraction>) entry
//                    .getKey()).getKey();
//            Fraction prob = ((Pair<TRSTerm, Fraction>) entry.getKey()).getValue();
//            Integer amount = entry.getValue();
//
//            // Create stdTerm
//            final ImmutablePair<? extends TRSTerm, Integer> stdRTermAndInt = coupledSetTermElement.y
//                    .renumberVariables(map, TRSTerm.STANDARD_PREFIX, nextFreeNr);
//            nextFreeNr = stdRTermAndInt.y;
//
//            // Create stdSet
//            Set<Pair<TRSFunctionApplication, Position>> stdSet = new HashSet<Pair<TRSFunctionApplication, Position>>();
//            for (Pair<TRSFunctionApplication, Position> termPositionPair : coupledSetTermElement.x) {
//                final ImmutablePair<? extends TRSFunctionApplication, Integer> stdRTermInSetAndInt = termPositionPair.x
//                        .renumberVariables(map, TRSTerm.STANDARD_PREFIX, nextFreeNr);
//                nextFreeNr = stdRTermInSetAndInt.y;
//                stdSet.add(new Pair<TRSFunctionApplication, Position>(stdRTermInSetAndInt.x, termPositionPair.y));
//            }
//            Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> stdCoupledSetTermElement = new Pair<>(
//                    stdSet, stdRTermAndInt.x);
//            stdProbabilityMap.put(
//                    new Pair<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>, Fraction>(
//                            stdCoupledSetTermElement, prob),
//                    amount);
//        }
//        MultiDistribution<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>> stdDist = new MultiDistribution<>(
//                stdProbabilityMap)
//                        .getCanonicalRepresentation();
//        if (!stdDist.equals(stdR)) {
//            System.err.println(
//                    l + " -> " + r + " --- >>> " + resultStdLHS + " -> " + stdDist + " -- >> " + stdR + " / " + map);
//        }
//        return stdDist.equals(stdR);
    }


    /**
     * renames the variables with given prefix and numbers starting from STANDARD_NUMBER.
     * E.g. for rule = f(x,y,x1,y) -> f(y,x,x,a), prefix = x and STANDARD_NUMBER = 0
     * we obtain f(x0,x1,x2,x1) -> f(x1,x0,x0,a).
     *
     * The standard representation of a rule is
     * rule.getWithRenumberedVariables(STANDARD_PREFIX);
     * 
     * @param prefix
     * @return a new dependency tuple with canonicalized variables
     */
    public CoupledPosDepTuple getWithRenumberedVariables(final String prefix) {
        var res = CoupledPosDepTuple.standardise_vars(l, r, prefix);
        return new CoupledPosDepTuple(
            res.x,
            res.y,
            this.stdL,
            this.stdR
        );

//        final Map<TRSVariable, TRSVariable> map = new HashMap<>();
//
//        // Create stdLHS
//        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLOneAndInt = l.x
//                .renumberVariables(map, prefix, TRSTerm.STANDARD_NUMBER);
//        Integer nextFreeNr = stdLOneAndInt.y;
//        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLTwoAndInt = l.y
//                .renumberVariables(map, prefix, nextFreeNr);
//        nextFreeNr = stdLTwoAndInt.y;
//        Pair<TRSFunctionApplication, TRSFunctionApplication> resultStdLHS = new Pair<TRSFunctionApplication, TRSFunctionApplication>(
//                stdLOneAndInt.x,
//                stdLTwoAndInt.x);
//
//        // Create stdRHS
//        final HashMultiSet<Pair<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>, Fraction>> stdProbabilityMap = new HashMultiSet<>();
//        for (Entry<?, Integer> entry : r.getProbabilityMapping().entrySet()) {
//            Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledSetTermElement = ((Pair<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>, Fraction>) entry
//                    .getKey()).getKey();
//            Fraction prob = ((Pair<TRSTerm, Fraction>) entry.getKey()).getValue();
//            Integer amount = entry.getValue();
//
//            // Create stdTerm
//            final ImmutablePair<? extends TRSTerm, Integer> stdRTermAndInt = coupledSetTermElement.y
//                    .renumberVariables(map, prefix, nextFreeNr);
//            nextFreeNr = stdRTermAndInt.y;
//
//            // Create stdSet
//            Set<Pair<TRSFunctionApplication, Position>> stdSet = new HashSet<Pair<TRSFunctionApplication, Position>>();
//            for (Pair<TRSFunctionApplication, Position> termPositionPair : coupledSetTermElement.x) {
//                final ImmutablePair<? extends TRSFunctionApplication, Integer> stdRTermInSetAndInt = termPositionPair.x
//                        .renumberVariables(map, prefix, nextFreeNr);
//                nextFreeNr = stdRTermInSetAndInt.y;
//                stdSet.add(new Pair<TRSFunctionApplication, Position>(stdRTermInSetAndInt.x, termPositionPair.y));
//            }
//            Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> stdCoupledSetTermElement = new Pair<>(
//                    stdSet, stdRTermAndInt.x);
//            stdProbabilityMap.put(
//                    new Pair<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>, Fraction>(
//                            stdCoupledSetTermElement, prob),
//                    amount);
//        }
//        return new CoupledPosDepTuple(resultStdLHS,
//                new MultiDistribution<>(stdProbabilityMap).getCanonicalRepresentation(), this.stdL,
//                this.stdR);
    }


    // ================================================================================
    // Utility
    // ================================================================================

    @Override
    public String export(Export_Util eu) {
        // Need to build string manually because C is a set
        // Planned result:
        // "(l#, l) -> ({(t#, pi)*}, r)"
        StringBuilder sb = new StringBuilder();
        // TODO: preallocate capacity, though others seem not to do that

        sb.append('(')
            .append(l.x.export(eu))
            .append(',')
            .append(l.y.export(eu))
            .append(") ")
            .append(eu.rightarrow())
            .append(" ({");

        // wow java actually has no decent iterators
        // so this is what I resort to
        String comma = "";
        for (Pair<TRSFunctionApplication, Position> pdt : this.getC()) {
            sb.append(comma)
                .append('(')
                .append(pdt.x.export(eu))
                .append(',')
                .append(pdt.y.export(eu))
                .append(")");
            comma = ",";
        }
        
        sb.append("},")
            .append(r.y.export(eu))
            .append(')');

        return sb.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * Two dependency tuples are considered equal if their canonicalized left hand side and right hand sides are equal.
     */
    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof CoupledPosDepTuple) {
            final CoupledPosDepTuple rule = (CoupledPosDepTuple) other;
            return this.hashCode == rule.hashCode && this.stdL.equals(rule.stdL) && this.stdR.equals(rule.stdR);
        }
        return false;
    }

    // TODO: How can you compare two rules? What order to we use for this? Why is
    // this necessary?
    @Override
    public final int compareTo(RuleSchema other) {
        // TODO Auto-generated method stub
        return 0;
    }

    @Override
    public Element toDOM(Document doc, XMLMetaData xmlMetaData) {
        final Element e = XMLTag.RULE.createElement(doc);

        final Element lhsPairElement = XMLTag.PAIR.createElement(doc);
        lhsPairElement.appendChild(this.l.x.toDOM(doc, xmlMetaData));
        lhsPairElement.appendChild(this.l.y.toDOM(doc, xmlMetaData));
        e.appendChild(lhsPairElement);

        final Element rhsPairElement = XMLTag.DISTRIBUTION.createElement(doc);
//        for (Entry<?, Integer> entry : r.getProbabilityMapping().entrySet()) {  // TODO
//            final Element probPairElement = XMLTag.PAIR.createElement(doc);
//            final Element setTermPairElement = XMLTag.PAIR.createElement(doc);
//            final Element probElement = XMLTag.FRACTION.createElement(doc);
//
//            Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledSetTermElement = ((Pair<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>, Fraction>) entry
//                    .getKey()).getKey();
//            Fraction prob = ((Pair<TRSTerm, Fraction>) entry.getKey()).getValue();
//            Integer amount = entry.getValue();
//
//            probElement.appendChild(XMLTag.createInteger(doc, prob.getNumerator()));
//            probElement.appendChild(XMLTag.createInteger(doc, prob.getDenominator()));
//
//            final Element setElement = XMLTag.SET.createElement(doc);
//            for (Pair<TRSFunctionApplication, Position> termPositionPair : coupledSetTermElement.x) {
//                final Element termPosPairElement = XMLTag.PAIR.createElement(doc);
//                termPosPairElement.appendChild(termPositionPair.x.toDOM(doc, xmlMetaData));
//                termPosPairElement.appendChild(termPositionPair.y.toDOM(doc, xmlMetaData));
//
//                setElement.appendChild(termPosPairElement);
//            }
//            setTermPairElement.appendChild(setElement);
//            setTermPairElement.appendChild(coupledSetTermElement.y.toDOM(doc, xmlMetaData));
//
//            probPairElement.appendChild(probElement);
//            probPairElement.appendChild(setTermPairElement);
//
//            for (int i = 0; i < amount; i++) {
//                rhsPairElement.appendChild(probPairElement);
//            }
//        }
        e.appendChild(rhsPairElement);

        return e;
    }

    @Override
    public Element toCPF(Document doc, XMLMetaData xmlMetaData) {
        final Element e = XMLTag.RULE.createElement(doc);

        final Element lhsPairElement = XMLTag.PAIR.createElement(doc);
        lhsPairElement.appendChild(this.l.x.toCPF(doc, xmlMetaData));
        lhsPairElement.appendChild(this.l.y.toCPF(doc, xmlMetaData));
        final Element lhs = CPFTag.LHS.createElement(doc);
        lhs.appendChild(lhsPairElement);
        e.appendChild(lhs);

        final Element rhsPairElement = XMLTag.DISTRIBUTION.createElement(doc);
//        for (Entry<?, Integer> entry : r.getProbabilityMapping().entrySet()) {  // TODO
//            final Element probPairElement = XMLTag.PAIR.createElement(doc);
//            final Element setTermPairElement = XMLTag.PAIR.createElement(doc);
//            final Element probElement = XMLTag.FRACTION.createElement(doc);
//
//            Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledSetTermElement = ((Pair<Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>, Fraction>) entry
//                    .getKey()).getKey();
//            Fraction prob = ((Pair<TRSTerm, Fraction>) entry.getKey()).getValue();
//            Integer amount = entry.getValue();
//
//            probElement.appendChild(XMLTag.createInteger(doc, prob.getNumerator()));
//            probElement.appendChild(XMLTag.createInteger(doc, prob.getDenominator()));
//
//            final Element setElement = XMLTag.SET.createElement(doc);
//            for (Pair<TRSFunctionApplication, Position> termPositionPair : coupledSetTermElement.x) {
//                final Element termPosPairElement = XMLTag.PAIR.createElement(doc);
//                termPosPairElement.appendChild(termPositionPair.x.toCPF(doc, xmlMetaData));
//                termPosPairElement.appendChild(termPositionPair.y.toCPF(doc, xmlMetaData));
//
//                setElement.appendChild(termPosPairElement);
//            }
//            setTermPairElement.appendChild(setElement);
//            setTermPairElement.appendChild(coupledSetTermElement.y.toCPF(doc, xmlMetaData));
//
//            probPairElement.appendChild(probElement);
//            probPairElement.appendChild(setTermPairElement);
//
//            for (int i = 0; i < amount; i++) {
//                rhsPairElement.appendChild(probPairElement);
//            }
//        }
        final Element rhs = CPFTag.RHS.createElement(doc);
        rhs.appendChild(rhsPairElement);
        e.appendChild(rhs);

        return e;
    }
}
