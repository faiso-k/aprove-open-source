package aprove.verification.dpframework.BasicStructures;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;
import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * This is nearly the same class as CoupledPosDepTuple. The only difference
 * is that we are additionally storing the Capped terms in the right-hand side.
 * (Needed in the DependencyGraph for the UsablePairs Processor)
 * 
 * For detailed comments of everything
 * 
 * @see CoupledPosDepTuple
 * 
 * @author Grigory Vartanyan
 * @version $Id$
 */
public class CappedCoupledPosDepTuple extends RuleSchema implements
        Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    private final Pair<TRSFunctionApplication, TRSFunctionApplication> l;

    private final Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> r;

    /* computed values */
    private final Pair<TRSFunctionApplication, TRSFunctionApplication> stdL;

    private final Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> stdR;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    protected CappedCoupledPosDepTuple(Pair<TRSFunctionApplication, TRSFunctionApplication> l,
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> r,
            Pair<TRSFunctionApplication, TRSFunctionApplication> stdL,
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> stdR) {
        this.l = l;
        this.r = r;

        if (Globals.useAssertions) {
            final boolean res = CappedCoupledPosDepTuple.checkProperLandR(l, r);
            assert (res);
            assert ((stdL == null && stdR == null) || (stdL != null && stdR != null));
        }

        if (stdL == null) {
            ImmutablePair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm>> stdLR = makeStdLR(
                    l,
                    r);

            this.stdL = stdLR.x;
            this.stdR = stdLR.y;
        } else {
            // don't trust the user
            if (Globals.useAssertions) {
                final boolean res = CappedCoupledPosDepTuple.checkProperStd(this.l, stdL, this.r, stdR);
                assert (res);
            }
            this.stdL = stdL;
            this.stdR = stdR;
        }

        this.hashCode = 493211 * this.stdL.hashCode() + 12452 * this.stdR.hashCode() + 732150386;
    }

    public static CappedCoupledPosDepTuple create(Pair<TRSFunctionApplication, TRSFunctionApplication> l,
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> r) {
        return new CappedCoupledPosDepTuple(l, r, null, null);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    public CappedCoupledPosDepTuple getStandardRepresentation() {
        // should be equivalent to getWithRenumberedVariables(STANDARD_PREFIX);
        return new CappedCoupledPosDepTuple(this.stdL, this.stdR, this.stdL, this.stdR);
    }

    public Pair<TRSFunctionApplication, TRSFunctionApplication> getLeftPair() {
        return l;
    }

    @Override
    public TRSFunctionApplication getLeft() {
        return l.y;
    }

    public TRSFunctionApplication getTupleLeft() {
        return l.x;
    }

    @Override
    public TRSFunctionApplication getLhsInStandardRepresentation() {
        return stdL.y;
    }

    public TRSFunctionApplication getTupleLhsInStandardRepresentation() {
        return stdL.x;
    }

    public Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> getRight() {
        return r;
    }

    @Override
    public Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> getRhsInStandardRepresentation() {
        // TODO Auto-generated method stub
        return stdR;
    }

    private static boolean checkProperLandR(Pair<TRSFunctionApplication, TRSFunctionApplication> l,
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> r) {
        return l != null && l.x != null && l.y != null && r != null;
        // TODO: Do we have to check everything?
    }

    @Override
    public Set<TRSTerm> getTerms() {
        final Set<TRSTerm> res = new LinkedHashSet<>();
        res.add(this.l.getKey());
        res.add(this.l.getValue());
//        for (Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> outerPair : r.getSupport()) {
            res.add(this.r.getValue());
            Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> depSet = this.r.getKey();
            for (Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position> pair : depSet) {
                res.add(pair.x.x);
                res.add(pair.x.y);
            }
//        }
        return res;
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        final Set<FunctionSymbol> res = new LinkedHashSet<>();
        res.addAll(this.l.getKey().getFunctionSymbols());
        res.addAll(this.l.getValue().getFunctionSymbols());
//        for (Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> outerPair : r.getSupport()) {
            res.addAll(this.r.getValue().getFunctionSymbols());
            Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> depSet = this.r.getKey();
            for (Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position> pair : depSet) {
                res.add(pair.x.x.getFunctionSymbol());
                res.add(pair.x.y.getFunctionSymbol());
            }
//        }
        return res;
    }

    @Override
    public Set<TRSVariable> getVariables() {
        final Set<TRSVariable> res = new LinkedHashSet<>();
        res.addAll(this.l.getKey().getVariables());
        res.addAll(this.l.getValue().getVariables());
//        for (Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> outerPair : r.getSupport()) {
            res.addAll(this.r.getValue().getVariables());
            Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> depSet = this.r.getKey();
            for (Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position> pair : depSet) {
                res.addAll(pair.x.x.getVariables());
                res.addAll(pair.x.y.getVariables());
            }
//        }
        return res;
    }

    public Set<TRSFunctionApplication> getAllTupleTermsInRHS() {
        final Set<TRSFunctionApplication> res = new LinkedHashSet<>();
//        for (Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> outerPair : r
//                .getSupport()) {
            Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> depSet = this.r.getKey();
            for (Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position> innerPair : depSet) {
                res.add(innerPair.x.y);
            }
//        }
        return res;
    }

    public Set<TRSFunctionApplication> getAllCappedTupleTermsInRHS() {
        final Set<TRSFunctionApplication> res = new LinkedHashSet<>();
//        for (Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> outerPair : r
//                .getSupport()) {
            Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> depSet = this.r.getKey();
            for (Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position> innerPair : depSet) {
                res.add(innerPair.x.x);
            }
//        }
        return res;
    }

    public CappedCoupledPosDepTuple removeTupleTermFromRHS(TRSFunctionApplication t) {
        // Create new RHS
//        final HashMultiSet<Pair<Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm>, Fraction>> newProbabilityMap = new HashMultiSet<>();
//        for (Entry<?, Integer> entry : stdR.getProbabilityMapping().entrySet()) {
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> coupledSetTermElement = this.r;
//            Fraction prob = ((Pair<TRSTerm, Fraction>) entry.getKey()).getValue();
//            Integer amount = entry.getValue();

            // Remove every occurrence of t from the RHS
            Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> stdSet = new HashSet<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>();
            for (Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position> termPositionPair : coupledSetTermElement.x) {
                if (!termPositionPair.x.y.equals(t)) {
                    stdSet.add(new Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>(
                            termPositionPair.x, termPositionPair.y));
                }
            }
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> resRHS = new Pair<>(
                    stdSet,
                    coupledSetTermElement.y);
//            newProbabilityMap.put(
//                    new Pair<Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm>, Fraction>(
//                            stdCoupledSetTermElement,
//                            prob),
//                    amount);
//        }

        final Pair<TRSFunctionApplication, TRSFunctionApplication> resLHS = this.getLeftPair();
//        final Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> resRHS = new MultiDistribution<>(
//                newProbabilityMap);
        return CappedCoupledPosDepTuple.create(resLHS, resRHS);
    }

    @Override
    public FunctionSymbol getRootSymbol() {
        return l.y.getRootSymbol();
    }

    public FunctionSymbol getTupleRootSymbol() {
        return l.x.getRootSymbol();
    }

    // ================================================================================
    // canonicalization
    // ================================================================================

    private ImmutablePair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm>> makeStdLR(
            Pair<TRSFunctionApplication, TRSFunctionApplication> l,
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> r) {
        final Map<TRSVariable, TRSVariable> map = new HashMap<>();

        // Create stdLHS
        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLOneAndInt = l.x.renumberVariables(map,
                TRSTerm.STANDARD_PREFIX,
                TRSTerm.STANDARD_NUMBER);
        Integer nextFreeNr = stdLOneAndInt.y;
        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLTwoAndInt = l.y.renumberVariables(map,
                TRSTerm.STANDARD_PREFIX, nextFreeNr);
        nextFreeNr = stdLTwoAndInt.y;
        Pair<TRSFunctionApplication, TRSFunctionApplication> resultStdLHS = new Pair<TRSFunctionApplication, TRSFunctionApplication>(
                stdLOneAndInt.x,
                stdLTwoAndInt.x);

        // Create stdRHS
//        final HashMultiSet<Pair<Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm>, Fraction>> stdProbabilityMap = new HashMultiSet<>();
//        for (Entry<?, Integer> entry : r.getProbabilityMapping().entrySet()) {
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> coupledSetTermElement = this.r;
//            Fraction prob = ((Pair<TRSTerm, Fraction>) entry.getKey()).getValue();
//            Integer amount = entry.getValue();

            // Create stdTerm
            final ImmutablePair<? extends TRSTerm, Integer> stdRTermAndInt = coupledSetTermElement.y
                    .renumberVariables(map, TRSTerm.STANDARD_PREFIX,
                            nextFreeNr);
            nextFreeNr = stdRTermAndInt.y;

            // Create stdSet
            Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> stdSet = new HashSet<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>();
            for (Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position> termPositionPair : coupledSetTermElement.x) {
                final ImmutablePair<? extends TRSFunctionApplication, Integer> stdRTermInSetAndIntCapped = termPositionPair.x.x
                        .renumberVariables(map,
                                TRSTerm.STANDARD_PREFIX,
                                nextFreeNr);
                final ImmutablePair<? extends TRSFunctionApplication, Integer> stdRTermInSetAndInt = termPositionPair.x.y
                        .renumberVariables(map,
                                TRSTerm.STANDARD_PREFIX,
                                nextFreeNr);
                nextFreeNr = stdRTermInSetAndInt.y;
                stdSet.add(new Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>(
                        new Pair<>(stdRTermInSetAndIntCapped.x,
                                stdRTermInSetAndInt.x),
                        termPositionPair.y));
            }
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> stdCoupledSetTermElement = new Pair<>(
                    stdSet,
                    stdRTermAndInt.x);
//            stdProbabilityMap.put(
//                    new Pair<Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm>, Fraction>(
//                            stdCoupledSetTermElement,
//                            prob),
//                    amount);
//        }
        return new ImmutablePair<>(resultStdLHS, stdCoupledSetTermElement);
    }

    private static boolean checkProperStd(Pair<TRSFunctionApplication, TRSFunctionApplication> l,
            Pair<TRSFunctionApplication, TRSFunctionApplication> stdL,
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> r,
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> stdR) {
        if (stdL == null || stdR == null) {
            return false;
        }
        final Map<TRSVariable, TRSVariable> map = new HashMap<>();

        // Check stdLHS
        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLOneAndInt = l.x.renumberVariables(map,
                TRSTerm.STANDARD_PREFIX,
                TRSTerm.STANDARD_NUMBER);
        Integer nextFreeNr = stdLOneAndInt.y;
        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLTwoAndInt = l.y.renumberVariables(map,
                TRSTerm.STANDARD_PREFIX, nextFreeNr);
        nextFreeNr = stdLTwoAndInt.y;
        Pair<TRSFunctionApplication, TRSFunctionApplication> resultStdLHS = new Pair<TRSFunctionApplication, TRSFunctionApplication>(
                stdLOneAndInt.x,
                stdLTwoAndInt.x);

        if (!resultStdLHS.equals(stdL)) {
            return false;
        }

        // Check stdRHS
//        final HashMultiSet<Pair<Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm>, Fraction>> stdProbabilityMap = new HashMultiSet<>();
//        for (Entry<?, Integer> entry : r.getProbabilityMapping().entrySet()) {
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> coupledSetTermElement = r;
//            Fraction prob = ((Pair<TRSTerm, Fraction>) entry.getKey()).getValue();
//            Integer amount = entry.getValue();

            // Create stdTerm
            final ImmutablePair<? extends TRSTerm, Integer> stdRTermAndInt = coupledSetTermElement.y
                    .renumberVariables(map, TRSTerm.STANDARD_PREFIX,
                            nextFreeNr);
            nextFreeNr = stdRTermAndInt.y;

            // Create stdSet
            Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> stdSet = new HashSet<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>();
            for (Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position> termPositionPair : coupledSetTermElement.x) {
                final ImmutablePair<? extends TRSFunctionApplication, Integer> stdRTermInSetAndIntCapped = termPositionPair.x.x
                        .renumberVariables(map,
                                TRSTerm.STANDARD_PREFIX,
                                nextFreeNr);
                final ImmutablePair<? extends TRSFunctionApplication, Integer> stdRTermInSetAndInt = termPositionPair.x.y
                        .renumberVariables(map,
                                TRSTerm.STANDARD_PREFIX,
                                nextFreeNr);
                nextFreeNr = stdRTermInSetAndInt.y;
                stdSet.add(new Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>(
                        new Pair<>(stdRTermInSetAndIntCapped.x,
                                stdRTermInSetAndInt.x),
                        termPositionPair.y));
            }
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> stdDist = new Pair<>(
                    stdSet,
                    stdRTermAndInt.x);
//            stdProbabilityMap.put(
//                    new Pair<Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm>, Fraction>(
//                            stdCoupledSetTermElement,
//                            prob),
//                    amount);
//        }
//        Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> stdDist = stdCoupledSetTermElement;
        if (!stdDist.equals(stdR)) {
            System.err.println(
                    l + " -> " + r + " --- >>> " + resultStdLHS + " -> " + stdDist + " -- >> " + stdR + " / " + map);
        }
        return stdDist.equals(stdR);
    }

    public CappedCoupledPosDepTuple getWithRenumberedVariables(final String prefix) {
        final Map<TRSVariable, TRSVariable> map = new HashMap<>();

        // Create stdLHS
        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLOneAndInt = l.x.renumberVariables(map,
                prefix, TRSTerm.STANDARD_NUMBER);
        Integer nextFreeNr = stdLOneAndInt.y;
        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLTwoAndInt = l.y.renumberVariables(map,
                prefix, nextFreeNr);
        nextFreeNr = stdLTwoAndInt.y;
        Pair<TRSFunctionApplication, TRSFunctionApplication> resultStdLHS = new Pair<TRSFunctionApplication, TRSFunctionApplication>(
                stdLOneAndInt.x,
                stdLTwoAndInt.x);

        // Create stdRHS
//        final Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> stdProbabilityMap = new HashMultiSet<>();
//        for (Entry<?, Integer> entry : r.getProbabilityMapping().entrySet()) {
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> coupledSetTermElement = r;
//            Fraction prob = ((Pair<TRSTerm, Fraction>) entry.getKey()).getValue();
//            Integer amount = entry.getValue();

            // Create stdTerm
            final ImmutablePair<? extends TRSTerm, Integer> stdRTermAndInt = coupledSetTermElement.y
                    .renumberVariables(map, prefix, nextFreeNr);
            nextFreeNr = stdRTermAndInt.y;

            // Create stdSet
            Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> stdSet = new HashSet<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>();
            for (Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position> termPositionPair : coupledSetTermElement.x) {
                final ImmutablePair<? extends TRSFunctionApplication, Integer> stdRTermInSetAndIntCapped = termPositionPair.x.x
                        .renumberVariables(map,
                                prefix,
                                nextFreeNr);
                final ImmutablePair<? extends TRSFunctionApplication, Integer> stdRTermInSetAndInt = termPositionPair.x.y
                        .renumberVariables(map,
                                prefix,
                                nextFreeNr);
                nextFreeNr = stdRTermInSetAndInt.y;
                stdSet.add(new Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>(
                        new Pair<>(stdRTermInSetAndIntCapped.x,
                                stdRTermInSetAndInt.x),
                        termPositionPair.y));
            }
            Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm> stdCoupledSetTermElement = new Pair<>(
                    stdSet,
                    stdRTermAndInt.x);
//            stdProbabilityMap.put(
//                    new Pair<Pair<Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>>, ? extends TRSTerm>, Fraction>(
//                            stdCoupledSetTermElement,
//                            prob),
//                    amount);
//        }
        return new CappedCoupledPosDepTuple(resultStdLHS, stdCoupledSetTermElement, this.stdL, this.stdR);
//                new MultiDistribution<>(stdProbabilityMap).getCanonicalRepresentation(),
    }

    // ================================================================================
    // Utility
    // ================================================================================

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder();

//        int remConds = this.probabilityMap.size();
//        for (final Entry<Pair<T, Fraction>, Integer> entry : this.probabilityMap.entrySet()) {
            Set<Pair<Pair<TRSFunctionApplication, TRSFunctionApplication>, Position>> elem = this.r.getKey();
//            Fraction prob = entry.getKey().getValue();
//            Integer amount = entry.getValue();
//            for (int i = 0; i < amount; i++) {
//                sb.append(prob).append(' ').append(eu.colon()).append(' ');
                if (elem instanceof Exportable) {
                    sb.append(((Exportable) elem).export(eu));
                } else {
                    sb.append(elem.toString());
                }
//                if ((--remConds) > 0) {
//                    sb.append(' ').append(eu.probabilistiChoiceOperator()).append(' ');
//                }
//                if (i != amount - 1) {
//                    sb.append(' ').append(eu.colon()).append('+').append(eu.colon()).append(' ');
//                }
//            }
//        }

//        return sb.toString();
        
        
        
        return "(" + this.l.getKey().export(eu) + "," + this.l.getValue().export(eu) + ")" + " " + eu.rightarrow() + " "
//                + this.r.export(eu);
                + sb.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof CappedCoupledPosDepTuple) {
            final CappedCoupledPosDepTuple rule = (CappedCoupledPosDepTuple) other;
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
//        for (Entry<?, Integer> entry : r.getProbabilityMapping().entrySet()) {
            final Element probPairElement = XMLTag.PAIR.createElement(doc);
            final Element setTermPairElement = XMLTag.PAIR.createElement(doc);
            final Element probElement = XMLTag.FRACTION.createElement(doc);

            Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledSetTermElement = ((Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>) this.r.getKey());
//            Fraction prob = ((Pair<TRSTerm, Fraction>) entry.getKey()).getValue();
//            Integer amount = entry.getValue();

//            probElement.appendChild(XMLTag.createInteger(doc, prob.getNumerator()));
//            probElement.appendChild(XMLTag.createInteger(doc, prob.getDenominator()));

            final Element setElement = XMLTag.SET.createElement(doc);
            for (Pair<TRSFunctionApplication, Position> termPositionPair : coupledSetTermElement.x) {
                final Element termPosPairElement = XMLTag.PAIR.createElement(doc);
                termPosPairElement.appendChild(termPositionPair.x.toDOM(doc, xmlMetaData));
                termPosPairElement.appendChild(termPositionPair.y.toDOM(doc, xmlMetaData));

                setElement.appendChild(termPosPairElement);
            }
            setTermPairElement.appendChild(setElement);
            setTermPairElement.appendChild(coupledSetTermElement.y.toDOM(doc, xmlMetaData));

            probPairElement.appendChild(probElement);
            probPairElement.appendChild(setTermPairElement);

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
//        for (Entry<?, Integer> entry : r.getProbabilityMapping().entrySet()) {
            final Element probPairElement = XMLTag.PAIR.createElement(doc);
            final Element setTermPairElement = XMLTag.PAIR.createElement(doc);
            final Element probElement = XMLTag.FRACTION.createElement(doc);

            Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledSetTermElement = ((Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm>) r.getKey());
//            Fraction prob = ((Pair<TRSTerm, Fraction>) entry.getKey()).getValue();
//            Integer amount = entry.getValue();

//            probElement.appendChild(XMLTag.createInteger(doc, prob.getNumerator()));
//            probElement.appendChild(XMLTag.createInteger(doc, prob.getDenominator()));

            final Element setElement = XMLTag.SET.createElement(doc);
            for (Pair<TRSFunctionApplication, Position> termPositionPair : coupledSetTermElement.x) {
                final Element termPosPairElement = XMLTag.PAIR.createElement(doc);
                termPosPairElement.appendChild(termPositionPair.x.toCPF(doc, xmlMetaData));
                termPosPairElement.appendChild(termPositionPair.y.toCPF(doc, xmlMetaData));

                setElement.appendChild(termPosPairElement);
            }
            setTermPairElement.appendChild(setElement);
            setTermPairElement.appendChild(coupledSetTermElement.y.toCPF(doc, xmlMetaData));

            probPairElement.appendChild(probElement);
            probPairElement.appendChild(setTermPairElement);

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
