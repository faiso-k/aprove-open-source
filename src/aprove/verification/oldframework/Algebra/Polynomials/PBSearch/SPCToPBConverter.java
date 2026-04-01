package aprove.verification.oldframework.Algebra.Polynomials.PBSearch;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Converts SPCs and ranges for the indefinites to
 * Pseudo Boolean constraints.
 *
 * For details on the linearizations, a first pointer can be
 *   http://www.cril.univ-artois.fr/PB07/coding.html
 *
 * Search for the names "Fortet" and "Glover" in the context
 * of linearization of 0-1-programs / PB-constraints for more.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class SPCToPBConverter {

    private static Logger log =
        Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.PBSearch.SPCToPBConverter");

    private final boolean fortet;
    // true:  use Fortet's PB linearization
    // false: use Glover's PB linearization

    private Map<IndefinitePart, IndefinitePart> productCache;
    // map products to the variables that represent them

    // for generating our new Pseudo-Boolean indefinites
    // must be "x" b/c of the PB evaluation grammar
    public static final String PREFIX = "x";
    private int nextIndex = 1;

    private SPCToPBConverter(boolean fortet) {
        this.fortet = fortet;
        this.productCache = new HashMap<IndefinitePart, IndefinitePart>();
    }

    /**
     * @param fortet
     *               true: use Fortet's PB linearization<br>
     *              false: use Glover's PB linearization
     * @return a new SPCToPBConverter
     */
    public static SPCToPBConverter create(boolean fortet) {
        return new SPCToPBConverter(fortet);
    }


    /**
     * Converts a collection of SPCs (considered to be a conjunction)
     * along with range information for the indefinites (unknowns) to
     * a Pseudo Boolean problem with information for retrieving a
     * solution for the original problem from a solution for the PB
     * problem.
     *
     * @param spcs - to be converted to PB
     * @param ranges - special ranges for certain indefinites
     * @param defaultRange - ranges for indefinites that are not known
     *                       to ranges
     * @return
     *   w:  PB evaluation compliant linear objective function (to be maximized)
     *   x:  PB evaluation compliant (indefinites from x1 .. xn) linear
     *       Pseudo Boolean constraints<br>
     *   y:  maximum index n of the variables<br>
     *   z:  [original indefinite -> representing SimplePolynomial]
     */
    public Quadruple<SimplePolynomial, List<SimplePolyConstraint>, Integer, Map<String, SimplePolynomial>> toPseudoBoolean(Collection<SimplePolyConstraint> spcs,
            SimplePolynomial maximizeMe,
            Map<String, BigInteger> ranges, BigInteger defaultRange) {
        this.nextIndex = 1; // reset
        Quadruple<SimplePolynomial, List<SimplePolyConstraint>, List<SimplePolyConstraint>, Map<String, SimplePolynomial>> nonLinQuad;
        nonLinQuad = this.toNonLinearPB(spcs, maximizeMe, ranges, defaultRange);
        SimplePolynomial maxMeLin = this.nonLinPBtoLinPB(nonLinQuad.x, nonLinQuad.w, this.fortet, nonLinQuad.y);
        Quadruple<SimplePolynomial, List<SimplePolyConstraint>, Integer, Map<String, SimplePolynomial>> result;
        result = new Quadruple<SimplePolynomial, List<SimplePolyConstraint>, Integer, Map<String, SimplePolynomial>>(maxMeLin,
                nonLinQuad.y, this.nextIndex - 1, nonLinQuad.z);
        return result;
    }


    /**
     * Given range info for the indefinites, computes an equivalent version
     * of spcs where all indefinites range over {0, 1} and are named
     * xi for i = 1, 2, 3, ... (PB variables for PB evaluation)
     *
     * @param spcs
     * @param ranges
     * @param defaultRange
     * @return
     *      w: possibly non-linear objective function (to be maximized)<br>
     *      x: possibly non-linear constraints<br>
     *      y: definitely linear constraints<br>
     *      z: [original indefinites -> substituting SimplePolynomials]
     */
    private Quadruple<SimplePolynomial, List<SimplePolyConstraint>, List<SimplePolyConstraint>,
                Map<String, SimplePolynomial>> toNonLinearPB(Collection<SimplePolyConstraint> spcs,
                        SimplePolynomial maximizeMe,
                        Map<String, BigInteger> ranges, BigInteger defaultRange) {

        if (SPCToPBConverter.log.isLoggable(Level.FINEST)) {
            SPCToPBConverter.log.finest("About to convert " + spcs.size() + " SPCs to non-linear Pseudo Boolean constraints.\n");
        }

        long millis1, millis2;
        millis1 = System.currentTimeMillis();
        List<SimplePolyConstraint> resultNonLin = new ArrayList<SimplePolyConstraint>(spcs.size());
        List<SimplePolyConstraint> resultLin = new ArrayList<SimplePolyConstraint>();

        SPSubstitutor spSubstitutor = new SPSubstitutor();
        Set<String> indefs = new LinkedHashSet<String>();

        // first build the substitution ...
        for (SimplePolyConstraint spc : spcs) {
            SimplePolynomial sp = spc.getPolynomial();
            indefs.addAll(sp.getIndefinites());
        }
        if (maximizeMe != null) {
            indefs.addAll(maximizeMe.getIndefinites());
        }

        Map<String, SimplePolynomial> substitution = new LinkedHashMap<String, SimplePolynomial>(indefs.size());
        for (String indef : indefs) {
            BigInteger range = this.getRange(indef, ranges, defaultRange);
            // ... build the poly that will substitute indef
            // (necessary also for range 1, PB var must have
            // special names) ...
            SimplePolynomial substitute = this.indefToPB(indef, range);

            // ... store it ...
            substitution.put(indef, substitute);

            // ... and add a new linear constraint to limit range if necessary
            // (i.e., if range != 2^k - 1) ...
            if (range.add(BigInteger.ONE).bitCount() != 1) {
                SimplePolynomial limitingSP = SimplePolynomial.create(range).minus(substitute);
                SimplePolyConstraint limitingSPC = new SimplePolyConstraint(limitingSP, ConstraintType.GE);
                resultLin.add(limitingSPC);
            }
        }

        // ... then apply it
        for (SimplePolyConstraint spc : spcs) {
            SimplePolynomial sp = spc.getPolynomial();
            sp = spSubstitutor.substitute(sp, substitution);
            SimplePolyConstraint newSPC = new SimplePolyConstraint(sp, spc.getType());
            resultNonLin.add(newSPC);
        }

        // objective if we optimize
        SimplePolynomial maximizeMeNonLinPB;
        if (maximizeMe != null) {
            maximizeMeNonLinPB = spSubstitutor.substitute(maximizeMe, substitution);
        }
        else {
            maximizeMeNonLinPB = null;
        }

        // now remove exponents from resultNonLin products and
        // minimizeMeNonLinPB (a^n = a for n > 0)
        ListIterator<SimplePolyConstraint> nonLinCsIter = resultNonLin.listIterator();
        while (nonLinCsIter.hasNext()) {
            SimplePolyConstraint spc = nonLinCsIter.next();
            SimplePolynomial sp = spc.getPolynomial().stripExponents();
            nonLinCsIter.set(new SimplePolyConstraint(sp, spc.getType()));
        }
        if (maximizeMeNonLinPB != null) {
            maximizeMeNonLinPB = maximizeMeNonLinPB.stripExponents();
        }

        millis2 = System.currentTimeMillis();
        if (SPCToPBConverter.log.isLoggable(Level.FINEST)) {
            SPCToPBConverter.log.finest("Conversion to non-linear Pseudo Boolean constraints took " +
                    (millis2-millis1) + " ms.\n");
        }
        return new Quadruple<SimplePolynomial, List<SimplePolyConstraint>, List<SimplePolyConstraint>, Map<String, SimplePolynomial>>(maximizeMeNonLinPB,
                resultNonLin, resultLin, substitution);
    }


    /**
     * Linearization of non-linear {0, 1}-constraints as proposed by
     * Fortet / Glover.
     *
     * @param spcs - non-null, no null elements, indefs are assumed to range
     *  over {0, 1} and to be named "xi", i = 1, 2, 3, ...
     * @param fortet - true: use Fortet's method, false: use Glover's method
     * @param linConstraints - reference parameter; the produced constraints will be
     *  added to linConstraints: a list of equivalent *linear* SPCs
     * @return a linearized version of maximizeMe
     */
    private SimplePolynomial nonLinPBtoLinPB(Collection<SimplePolyConstraint> spcs,
            SimplePolynomial maximizeMe, boolean fortet,
            List<SimplePolyConstraint> linConstraints) {

        if (SPCToPBConverter.log.isLoggable(Level.FINEST)) {
            SPCToPBConverter.log.finest("About to linearize " + spcs.size() + " SPCs using "
                    + (fortet ? "Fortet" : "Glover") + "\'s method.\n" );
        }
        int oldSize = linConstraints.size();

        // for each SP
        // * replace each product pr by a representing variable y_pr
        // * add linear inequalities that state that pr = y_pr

        long millis1, millis2;
        millis1 = System.currentTimeMillis();
        for (SimplePolyConstraint spc : spcs) {
            SimplePolynomial sp = spc.getPolynomial();
            SimplePolynomial newSP = this.linearize(sp, linConstraints);
            linConstraints.add(new SimplePolyConstraint(newSP, spc.getType()));
        }
        SimplePolynomial maxMeLin;
        if (maximizeMe == null) {
            maxMeLin = null;
        }
        else {
            maxMeLin = this.linearize(maximizeMe, linConstraints);
        }
        millis2 = System.currentTimeMillis();
        if (SPCToPBConverter.log.isLoggable(Level.FINEST)) {
            SPCToPBConverter.log.finest("Linearization took " + (millis2-millis1) +
                    " ms and yielded " + (linConstraints.size() - oldSize) +
                    " new linear constraints.\n");
        }
        return maxMeLin;
    }

    /**
     * Linearizes a SimplePolynomial with unknowns over {0, 1}.
     *
     * @param nonLinear - non-linear polynomial where the unknowns are
     *  assumed to range over {0, 1}
     * @param linConstraints - here side constraints are added
     * @return a linearized version of nonLinear, possibly containing
     *  fresh Diophantine varibles which are further constrained by
     *  side constraints added to linConstraints
     */
    private SimplePolynomial linearize(SimplePolynomial nonLinear,
            List<SimplePolyConstraint> linConstraints) {
        ImmutableMap<IndefinitePart, BigInteger> simpleMonomials = nonLinear.getSimpleMonomials();
        Map<IndefinitePart, BigInteger> newSPmap = new LinkedHashMap<IndefinitePart, BigInteger>(simpleMonomials.size());
        for (Entry<IndefinitePart, BigInteger> monomial : simpleMonomials.entrySet()) {
            IndefinitePart product = monomial.getKey();
            IndefinitePart representativeOfProduct;
            if (product.size() <= 1) { // at most one PB variable: okay
                representativeOfProduct = product;
            }
            else { // more than 1 variable: linearize
                representativeOfProduct = this.productCache.get(product);
                if (representativeOfProduct == null) {
                    // build a new representative ...
                    String newName = this.nextName();
                    representativeOfProduct = IndefinitePart.create(newName, 1);
                    this.productCache.put(product, representativeOfProduct);

                    // ... and the corresponding linear PB constraints,
                    // adding the latter to linConstraints in the process
                    this.productGEy(product, representativeOfProduct, linConstraints);
                    if (this.fortet) {
                        this.yGEproductFortet(product, representativeOfProduct, linConstraints);
                    }
                    else {
                        this.yGEproductGlover(product, representativeOfProduct, linConstraints);
                    }
                }
            }
            newSPmap.put(representativeOfProduct, monomial.getValue());
        }
        SimplePolynomial newSP = SimplePolynomial.create(newSPmap);
        return newSP;
    }

    /**
     * Adds a linear PB-constraint to linSpcs that states that product >= y.
     *
     * Let product = x1*...*xn.
     * Then the constraint y - (sum xi) + (n - 1) >= 0 is added.
     *
     * @param product
     * @param y
     * @param linSpcs
     */
    private void productGEy(IndefinitePart product, IndefinitePart y,
            List<SimplePolyConstraint> linSpcs) {
        ImmutableMap<String, Integer> exps = product.getExponents();
        int size = exps.size();
        Map<IndefinitePart, BigInteger> resultSP = new LinkedHashMap<IndefinitePart, BigInteger>(size+2);
        int addend = size - 1;
        for (String a : exps.keySet()) {
            IndefinitePart newIP = IndefinitePart.create(a, 1);
            resultSP.put(newIP, BigInteger.valueOf(-1));
        }
        resultSP.put(y, BigInteger.ONE);
        resultSP.put(IndefinitePart.ONE, BigInteger.valueOf(addend));
        linSpcs.add(new SimplePolyConstraint(SimplePolynomial.create(resultSP),
                    ConstraintType.GE));
    }

    /**
     * Adds a linear PB-constraint to linSpcs that states that y >= product.
     * -> Fortet's method.
     *
     * Let product = x1*...*xn.
     * Then the constraint (sum xi) - n*y >= 0 is added.
     *
     * @param product
     * @param y
     * @param linSpcs
     */
    private void yGEproductFortet(IndefinitePart product, IndefinitePart y,
            List<SimplePolyConstraint> linSpcs) {
        ImmutableMap<String, Integer> exps = product.getExponents();
        int size = exps.size();
        Map<IndefinitePart, BigInteger> resultSP = new LinkedHashMap<IndefinitePart, BigInteger>(size+1);
        for (String a : exps.keySet()) {
            IndefinitePart newIP = IndefinitePart.create(a, 1);
            resultSP.put(newIP, BigInteger.ONE);
        }
        resultSP.put(y, BigInteger.valueOf(-size));
        linSpcs.add(new SimplePolyConstraint(SimplePolynomial.create(resultSP),
                ConstraintType.GE));
    }

    /**
     * Adds linear PB-constraints to linSpcs that state that y >= product.
     * -> Glover's method.
     *
     * Let product = x1*...*xn.
     * Then the constraints xi - y >= 0 are added for all i \in {1, ..., n}.
     *
     * @param product
     * @param y
     * @param linSpcs
     */
    private void yGEproductGlover(IndefinitePart product, IndefinitePart y,
            List<SimplePolyConstraint> linSpcs) {
        ImmutableMap<String, Integer> exps = product.getExponents();
        for (String a : exps.keySet()) {
            Map<IndefinitePart, BigInteger> aResultSP = new LinkedHashMap<IndefinitePart, BigInteger>(2);
            IndefinitePart newIP = IndefinitePart.create(a, 1);
            aResultSP.put(newIP, BigInteger.ONE);
            aResultSP.put(y, BigInteger.valueOf(-1));
            SimplePolyConstraint aResultSPC = new SimplePolyConstraint(SimplePolynomial.create(aResultSP),
                    ConstraintType.GE);
            linSpcs.add(aResultSPC);
        }
    }


    /**
     * @param indef
     * @param range
     * @return a fresh SimplePolynomial that encodes indef over range
     *  with indefinites assumed to range over 0 and 1.
     */
    private SimplePolynomial indefToPB(String indef, BigInteger range) {
        if (Globals.useAssertions) {
            assert range.signum() > 0;
            assert indef != null;
        }
        int bits = range.bitLength();
        Map<IndefinitePart, BigInteger> result = new LinkedHashMap<IndefinitePart, BigInteger>(bits);
        BigInteger twoToTheI = BigInteger.ONE;
        for (int i = 0; i < bits; ++i) {
            String newIndef = this.nextName();
            IndefinitePart newIP = IndefinitePart.create(newIndef, 1);
            result.put(newIP, twoToTheI);
            twoToTheI = twoToTheI.shiftLeft(1); // *2
        }
        return SimplePolynomial.create(result);
    }


    private BigInteger getRange(String a, Map<String, BigInteger> ranges,
            BigInteger defaultRange) {
        BigInteger r = ranges.get(a);
        return r == null ? defaultRange : r;
    }

    private String nextName() {
        String result = SPCToPBConverter.PREFIX + this.nextIndex;
        ++this.nextIndex;
        return result;
    }

}
