package aprove.verification.oldframework.Algebra.Polynomials;

import static aprove.verification.oldframework.Algebra.Polynomials.ConstraintType.*;
import static aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.SimplificationMode.*;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author Carsten Fuhs
 * @version $Id$
 *
 * A SimplePolyConstraintSimplifier is always created for two Sets of
 * SimplePolyConstraints: one of constraints which are to be solved "as such",
 * and one of constraints of type GE of which one will have to be oriented
 * strictly later on. Calling simplify() then converts these input sets
 * into equivalent, but (hopefully) simpler sets along with two maps
 * which indicate some already deduced equalities.
 *
 * One can parametrize which optimizations to make using the attribute level.
 *
 * Here the underlying assumption is that the unknowns of a SimplePolynomial
 * may only be instantiated with non-negative integers (aka natural numbers).
 */
public class SimplePolyConstraintSimplifier {

    public enum SimplificationMode {
        NONE, // nothing is done at all
        CONTEXT_FREE, // only perform simplifications that do not take into
                      // account the other constraints
        CONTEXT_SENSITIVE, // also perform simplifications that profit from
                           // knowledge derived from other constraints
        MAXIMUM // perfom all simplifications, including those
                                // that make use of the graph that consists of
                                // indefinites and numbers
    }

    // If the range for some indefinite exceeds this value, we do not perform
    // graph-based simplification since the graph would become too big
    // (i.e., instead of MAXIMUM, we do CONTEXT_SENSITIVE).
    // Note that the value of this constant must be representable as an int!
    private static final BigInteger MAX_RANGE_FOR_GRAPH = BigInteger.valueOf(20l);

    private SimplificationMode level;

    private static Logger log =
        Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier");


    // constraints which are likely to be too complex to be used
    // directly to simplify other constraints; may implicitly contain
    // such information

    private PrioritySet<SimplePolyConstraint> complexConstraints;
    // yet to be processed and checked for simplification helpers

    private Set<SimplePolyConstraint> processedComplexConstraints;
    // already processed by the *current* sets of useful constraints;
    // it will be necessary to retry with new useful constraints, though.

    private PrioritySet<SimplePolyConstraint> searchStrictConstraints;
    // constraints of type GE of which one will have to be ordered strictly,
    // but we have not figured out yet which one

    private Set<SimplePolyConstraint> processedSearchStrictConstraints;
    // constraints of type GE of which one will have to be ordered strictly,
    // but we have not figured out yet which one; these have already been
    // processed by the current set of useful constraints

    // sets of constraints of types GT (GE internally) and EQ which are assumed
    // to come in handy for simplification, already used by the
    // corresponding simplify methods, but potentially still needed

    private Set<SimplePolyConstraint> usefulGTConstraints;
    // elements must match a_i - 1 >= 0
    // The infix "GT", which will also be used in comments and identifiers
    // in this when referring to constraints that match a_i - 1 >= 0,
    // is derived from the purpose of this set:
    // Storing information about indefinites a_i known to be strictly greater
    // than zero.
    // (Note that the constructor of SimplePolyConstraint converts type GT to
    // GE, adapting the LHS polynomial suitably in the process.)

    private Set<SimplePolyConstraint> usefulEQConstraints1;
    // 1 addend

    private Set<SimplePolyConstraint> usefulEQConstraints2;
    // 2 addends, one of them numerical


    private LinkedList<SimplePolyConstraint> intermediateConstraints;
    // Constraints that occur while useful constraints are being
    // simplified or while their consistency is tested;
    // needs to be emptied before proceeding with the
    // simplification of complex constraints may continue.
    //
    // A data structure over which iteration is possible despite
    // *arbitrary* element removal and addition during the iteration
    // is needed here. Unfortunately, this means that e.g. HashSets
    // cannot be used here.
    //
    // One should insert constraints of type GT (GE internally)
    // at the head of intermediateConstraints and those of type EQ
    // at the tail (GT constraints can only be applied on other useful
    // constraints, whereas EQ constraints can also be
    // applied on complex constraints, so for the sake of efficiency,
    // GT constraints should be processed first.).
    // This is being relied upon in simplifyEQ1(...).
    //
    // Might be a good idea to write a wrapper for add* to enforce this.


    // for the new greater-than-graph framework of the simplifier:
    // foo -> bar means foo >= bar
    private Graph<GENode, Object> graph; // don't annotate edges

    // stores the node objects of the graph that represent numbers
    private GENode[] numericalNodeCache;

    // mark which constraints have already been analyzed for the graph
    private Set<SimplePolyConstraint> analyzedSPCsForGraph;

    // indefinite coefficient |-> value, where the indefinite coefficient
    // does not occur in this.*Constraints* any more
    private Map<String, BigInteger> valueMap;

    // map the indefinite that still occurs in the actual SimplePolyConstraints
    // to a set of other indefinites that have been replaced by the key
    // in the other SimplePolyConstraints
    private Map<String, Set<String>> refMap;

    // the search for a value for an indefinite coefficient a will take place
    // over the integer interval [0, range(a)]; this information will be
    // exploited for the graph construction
    private final DefaultValueMap<String, BigInteger> ranges;

    // derived value: maximum range that occurs in ranges
    private final BigInteger maxRange;

    // Do we build this.graph and use it for simplification?
    private boolean useGraph;

    // Are there any searchstrict constraints to be regarded
    // after calling the constructor?
    private boolean regardSearchStrictConstraints;

    /**
     * Constructs a SimplePolyConstraintSimplifier where inputConstraints
     * contains the SimplePolyConstraints that are to be simplified by this.
     *
     * @param inputConstraints - the constraints that are to be simplified
     * @param searchStrictConstraints - constraints of type GE of which one
     *  will have to be oriented strictly afterwards, but we don't know yet
     *  which one
     * @param ranges - the ranges over which the constraints are to be solved
     * @param stripExponentsForRangeOne - strip exponents if range == 1?
     *  (e.g., 7a^2b^3 - 2ab^8 + 9c^2 >= 0 becomes 5ab + 9c >= 0)
     */
    public SimplePolyConstraintSimplifier (Set<SimplePolyConstraint> inputConstraints,
                                           Set<SimplePolyConstraint> searchStrictConstraints,
                                           DefaultValueMap<String, BigInteger> ranges, boolean stripExponentsForRangeOne) {
        SimplePolyConstraintComparator comparator;
        comparator = new SimplePolyConstraintComparator();
        if (Globals.useAssertions) {
            for (SimplePolyConstraint spc : searchStrictConstraints) {
                assert (spc.getType() == GE);
            }
        }

        // find maximum range used here
        BigInteger highestRange = ranges.getDefaultValue();
        for (BigInteger specialRange : ranges.values()) {
            if (specialRange.compareTo(highestRange) > 0) {
                highestRange = specialRange;
            }
        }

        this.maxRange = highestRange;
        this.ranges = ranges;

        // experimental pre-simplification for range == 1:
        // reduce all exponents >= 1 to 1 (a^n = a, n > 0);
        // apply only if /all/ indefinites have range 1
        // (this should be doable also if there are some indefs
        // with other ranges since we can just leave them as
        //they are; maybe later)
        if (stripExponentsForRangeOne && highestRange.equals(BigInteger.ONE)) {
            PrioritySet<SimplePolyConstraint> strippedComplexSPCs;
            strippedComplexSPCs = new PrioritySet<SimplePolyConstraint>(comparator);
            for (SimplePolyConstraint spc : inputConstraints) {
                SimplePolynomial sp = spc.getPolynomial().stripExponents();
                strippedComplexSPCs.add(new SimplePolyConstraint(sp, spc.getType()));
            }
            this.complexConstraints = strippedComplexSPCs;

            PrioritySet<SimplePolyConstraint> strippedSearchStrictSPCs;
            strippedSearchStrictSPCs = new PrioritySet<SimplePolyConstraint>(comparator);
            for (SimplePolyConstraint spc : searchStrictConstraints) {
                SimplePolynomial sp = spc.getPolynomial().stripExponents();
                strippedSearchStrictSPCs.add(new SimplePolyConstraint(sp, spc.getType()));
            }
            this.searchStrictConstraints = strippedSearchStrictSPCs;
        }
        else {
            // first, we take all the constraints of inputConstraints and
            // treat them as complexConstraints that are yet to be processed
            this.complexConstraints = new PrioritySet<SimplePolyConstraint>(comparator,
                    inputConstraints);

            // store searchStrictConstraints separately.
            this.searchStrictConstraints = new PrioritySet<SimplePolyConstraint>(comparator,
                    searchStrictConstraints);
        }

        int searchStrictSize = this.searchStrictConstraints.size();
        switch (searchStrictSize) {
        case 0:
            this.regardSearchStrictConstraints = false;
            break;
        case 1: // only one searchstrict constraint
                // => will /have/ to be oriented strictly
            Iterator<SimplePolyConstraint> searchStrictIter = this.searchStrictConstraints.iterator();
            SimplePolyConstraint spc = searchStrictIter.next();
            this.complexConstraints.add(new SimplePolyConstraint(spc.getPolynomial(), GT));
            searchStrictIter.remove();
            this.regardSearchStrictConstraints = false;
            break;
        default:
            this.regardSearchStrictConstraints = true;
            break;
        }

        // the other sets/lists are initially empty
        this.processedComplexConstraints = new LinkedHashSet<SimplePolyConstraint>();
        this.processedSearchStrictConstraints = new LinkedHashSet<SimplePolyConstraint>();

        this.usefulGTConstraints = new LinkedHashSet<SimplePolyConstraint>();
        this.usefulEQConstraints1 = new LinkedHashSet<SimplePolyConstraint>();
        this.usefulEQConstraints2 = new LinkedHashSet<SimplePolyConstraint>();

        this.intermediateConstraints = new LinkedList<SimplePolyConstraint>();

        this.valueMap = new LinkedHashMap<String, BigInteger>();
        this.refMap = new LinkedHashMap<String, Set<String>>();
        this.useGraph = false;
        this.graph = null;
        this.analyzedSPCsForGraph = null;

        this.level = MAXIMUM;
        if (Globals.DEBUG_FUHS) {
            if (SimplePolyConstraintSimplifier.log.isLoggable(Level.FINER)) {
                SimplePolyConstraintSimplifier.log.log(Level.FINER, "SPCSimplifier created for " +
                        inputConstraints.size() + " ordinary SPCs and " +
                        searchStrictSize +
                        " searchstrict SPCs. Exponents have " +
                        ((stripExponentsForRangeOne && this.maxRange.equals(BigInteger.ONE)) ? "" : "not") +
                        " been stripped.\n");
            }
        }
    }

    public Quadruple<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>, Map<String, BigInteger>, Map<String, Set<String>>> simplify
            (SimplificationMode level, boolean simplifySearchStrict, Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert level != null;
        }
        if (level == MAXIMUM && this.maxRange.compareTo(SimplePolyConstraintSimplifier.MAX_RANGE_FOR_GRAPH) > 0) {
            this.level = CONTEXT_SENSITIVE;
        }
        else {
            this.level = level;
        }
        this.regardSearchStrictConstraints = this.regardSearchStrictConstraints && simplifySearchStrict;
        if ((! this.regardSearchStrictConstraints) &&
                (! this.searchStrictConstraints.isEmpty())) {
            this.processedSearchStrictConstraints.addAll(this.searchStrictConstraints);
            this.searchStrictConstraints.clear();
        }
        if (Globals.DEBUG_FUHS) {
            if (SimplePolyConstraintSimplifier.log.isLoggable(Level.FINER)) {
                SimplePolyConstraintSimplifier.log.log(Level.FINER, "SPCSimplifier: About to simplify in mode " + this.level +
                        "; searchstrict constraints are " +
                        (this.regardSearchStrictConstraints ? "" : "not ") +
                        "regarded.\n");
            }
        }
        return this.simplify(aborter);
    }


    /**
     * The main method of SimplePolyConstraintSimplifier.
     *
     * @return Quadruple of
     *  1) a simplified version of the searchStrictConstraints passed to the
     *     constructor (indefinites or products of indefinites for which
     *     further knowledge is obtained will be suitably replaced)
     *  2) a simplified representation of the constraints contained by the
     *     attributes of this, together with the knowledge in the other
     *     components of the result equivalent to the constraints
     *     this has been created with
     *  3) a mapping of indefinites to the values they must take according
     *     to the input constraints of this; these indefinites neither occur
     *     in the 1st nor in the 2nd component of the result
     *  4) a mapping of indefinites which still occur in the first component
     *     of the result to others which do not occur there any more; these
     *     other indefinites have occurred in the initial constraints, and
     *     it could be deduced that they must take the same value as their
     *     key in the mapping
     *  OR
     *     null if the initial constraints have been found to be unsatisfiable
     *     over {0, ..., this.range}
     */
    public Quadruple<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>, Map<String, BigInteger>, Map<String, Set<String>>> simplify
        (Abortion aborter) throws AbortionException {

        aborter.checkAbortion();

        if (this.level == NONE) {
            return new Quadruple<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>, Map<String, BigInteger>, Map<String, Set<String>>>
              (this.searchStrictConstraints, this.complexConstraints, this.valueMap, this.refMap);
        }

        this.useGraph = (this.level == MAXIMUM);
        if (this.useGraph) {
            this.initGraph();
            this.analyzedSPCsForGraph = new HashSet<SimplePolyConstraint>();
        }

        // outline:
        // repeat
        // * SimplePolyConstraint-based simplification:
        //   while there are complexConstraints waiting for processing:
        //   - remove such a constraint from these complexConstraints, say cc.
        //   - contextFreeSimplify(cc), putting the useful knowledge obtained
        //     from cc into intermediateConstraints for further processing
        //   - while there are intermediateConstraints:
        //     > remove such a constraint from intermediateConstraints, say uc.
        //     > check whether uc is consistent with the other useful constraints,
        //       possibly simplifying it in the process
        //     > simplify the other constraints with uc, possibly adding useful
        //       constraints to intermediateConstraints
        //
        //  (similar treatment for searchStrictConstraints, but take into account
        //  that one of them will have to be oriented strictly afterwards
        //  => if they are valid, remove and switch to non-searchstrict mode;
        //     don't divide by common factor, etc.)
        //
        // * graph-based simplification (if applicable given the number
        //   of input constraints of this):
        //   derive (from the SimplePolyConstraints) and maintain a graph whose
        //   nodes are indefinites and numbers and whose edges represent the >=
        //   relation (neglecting reflexive edges), goal: SCCs with more than
        //   one element mean that their contents are equal.
        //   for each such SCC, pick a node (preferably a number) and map
        //   - all the other nodes of the SCC to it in this.valueMap
        //     if it is a number
        //   - it to the set of all the other nodes of the SCC in this.refMap
        //     if it is an indefinite
        //   specialize the SimplePolyConstraints of this accordingly to contain
        //   none of the keys of this.valueMap and none of the elements of the
        //   values of this.refMap anymore
        // until either an inconsistency has been found (wrt satisfiability
        // over {0, ..., this.range}) or the graph-based simplification did not
        // yield any new non-trivial (neither valid nor trivially insatisfiable)
        // constraints
        //
        // in the end, replace a_i - 1 >= 0 by a_i |-> 1 in this.valueMap
        // if a_i only occurs in a_i - 1 >= 0, also map the elements of the
        // value of a_i in this.refMap to 1 in this.valueMap (if there are
        // such elements)


        boolean inconsistencyDetected; // Are the constraints inconsistent?

        boolean newConstraintBuiltViaGraph = true;
        // Do we have to iterate the process because the graph-based simplifier
        // has replaced a constraint by a simpler one?

        // DEBUG
        //int counter = 1;

        while (newConstraintBuiltViaGraph) {

            // DEBUG
            //System.out.println("iteration " + counter + " of outer simplify loop");
            //counter++;

            while ((! this.complexConstraints.isEmpty()) ||
                        (this.regardSearchStrictConstraints &&
                         !this.searchStrictConstraints.isEmpty()) ) {
                if (! this.complexConstraints.isEmpty()) {
                    SimplePolyConstraint complexConstraint = this.complexConstraints.poll();

                    // Perform a context-free simplification of complexConstraint.
                    // In the process, both new complex constraints and new
                    // useful constraints may be born, together being equivalent
                    // to the old complexConstraint. The complex constraints will
                    // be put into this.processedComplexConstraints, whereas the
                    // useful constraints will enter this.intermediateConstraints
                    // for further processing.

                    inconsistencyDetected = (! this.simplifyContextFree(complexConstraint));
                }
                else { // (! this.searchStrictConstraints.isEmpty()),
                       // see loop condition
                    SimplePolyConstraint searchStrictConstraint = this.searchStrictConstraints.poll();
                    // context-free simplification of searchStrictConstraint
                    inconsistencyDetected = (! this.simplifySearchStrictContextFree(searchStrictConstraint));
                }

                if (inconsistencyDetected) { // these constraints can't be satisfied
                    return null;             //  => give up
                }

                if (this.level == CONTEXT_FREE) {
                    this.processedComplexConstraints.addAll(this.intermediateConstraints);
                    this.intermediateConstraints.clear();
                    continue;
                    // This should keep us from all the context-sensitive stuff below.
                }

                // After the context-free simplification of
                // complexConstraint / searchStrictConstraint, we will
                // take care of the contents of this.intermediateConstraints
                // and use them to simplify all constraints of this on which
                // such simplifications are applicable.

                while (! this.intermediateConstraints.isEmpty()) {
                    SimplePolyConstraint usefulConstraint = this.intermediateConstraints.poll();
                    ConstraintType type = usefulConstraint.getType();
                    if (type.equals(EQ)) {
                        int numberOfAddends = usefulConstraint.numberOfAddends();
                        if (numberOfAddends == 1) {
                            inconsistencyDetected = (! this.simplifyEQ1(usefulConstraint, aborter));
                            if (inconsistencyDetected) {
                                return null;
                            }
                        }
                        else {
                            if (Globals.useAssertions) {
                                assert (numberOfAddends == 2);
                            }
                            inconsistencyDetected = (! this.simplifyEQ2(usefulConstraint));
                            if (inconsistencyDetected) {
                                return null;
                            }
                        }
                    }
                    else {
                        // per "definition" of useful constraints,
                        // type ought to be GE.
                        if (Globals.useAssertions) {
                            assert type.equals(GE);
                        }
                        inconsistencyDetected = (! this.simplifyGT(usefulConstraint));
                        if (inconsistencyDetected) {
                            return null;
                        }
                    }
                }
            }


            if (this.useGraph) {
                // Derive the constraint graph from the constraints of this.
                inconsistencyDetected = (! this.buildGraph());
                if (inconsistencyDetected) {
                    return null;
                }

                // Derive mappings from the graph, possibly eliminating some of
                // the constraints in the process.
                // Note that this might create some even simpler constraints which
                // then might be useful for yet another constraint-based fixpoint
                // iteration.

                Pair<Boolean, Boolean> graphResult = this.applyGraphSCCs();

                if (! graphResult.x) {
                    return null;
                }
                newConstraintBuiltViaGraph = graphResult.y;
            }
            else { // graph not used => no new constraints found using the graph
                newConstraintBuiltViaGraph = false;
            }
        }

        if (this.regardSearchStrictConstraints &&
            this.processedSearchStrictConstraints.isEmpty()) {
            return null;
        }

        // simplify a_i - 1 >= 0 for a_i not occurring in any other constraint
        this.simplifyGTsWhoseIndefiniteOccursNowhereElse();

        // now unite all sets in order to get the result
        this.processedComplexConstraints.addAll(this.usefulEQConstraints1);
        this.processedComplexConstraints.addAll(this.usefulEQConstraints2);
        this.processedComplexConstraints.addAll(this.usefulGTConstraints);

        if (Globals.DEBUG_FUHS) {
            if (SimplePolyConstraintSimplifier.log.isLoggable(Level.FINER)) {
                SimplePolyConstraintSimplifier.log.log(Level.FINER, "SPC simplification yielded " + this.processedComplexConstraints.size() +
                        " ordinary SPCs and " + this.processedSearchStrictConstraints.size() + " searchstrict SPCs\n");
            }
        }

        return new Quadruple<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>, Map<String, BigInteger>, Map<String, Set<String>>>(this.processedSearchStrictConstraints, this.processedComplexConstraints, this.valueMap, this.refMap);
    }


    /* first some methods for SimplePolyConstraint-based simplification
       for which this.graph is not used */

    /**
     * Simplifies a searchstrict constraint without regarding any other
     * constraints (context), puts the (hopefully) simplified constraint into
     * this.processedSearchStrictConstraints if there is a chance that it can
     * be oriented strictly (not all addends negative), may put some of the
     * resulting constraints into this.intermediateConstraints if they have
     * not been encountered before (e.g. if all addends are negative).
     * If false is returned, not all of the above mentioned tasks are
     * necessarily performed (pointless anyway).
     *
     * this.intermediateConstraints is assumed to be empty when
     * simplifySearchStrictConstextFree is called.
     *
     * @param inputConstraint searchstrict constraint (type GE)
     *  to be simplified
     * @return false in case the constraint turns out to be unsatisfiable,
     *  true otherwise
     */
    private boolean simplifySearchStrictContextFree (SimplePolyConstraint inputConstraint) {

        if (Globals.useAssertions) {
            assert(inputConstraint.getType() == GE);
            assert(this.intermediateConstraints.isEmpty());
        }
        // proceed similar to the case of non-searchstrict constraints
        // (see below), but with some modifications because we have to
        // make sure that we can still orient the constraints strictly
        // after all is said and done:

        // (1) all addends have positive factors => we might have found our strictly orientable constraint
        if (inputConstraint.allPositive()) {
            if (inputConstraint.getNumericalAddend().signum() > 0) {
                // even the strict version of inputConstraint will be valid, so
                // the candidate for strict orientation has been found.
                // make all other searchstrict constraints to "normal" ones
                // and we do not need to stay in searchstrict mode any more
                for (SimplePolyConstraint spc : this.searchStrictConstraints) {
                    this.complexConstraints.add(spc);
                }

                // some searchstrict constraints may be simplifiable
                // despite having been processed already
                this.complexConstraints.addAll(this.processedSearchStrictConstraints);
                this.searchStrictConstraints = new PrioritySet<SimplePolyConstraint>(new SimplePolyConstraintComparator());
                this.processedSearchStrictConstraints = new HashSet<SimplePolyConstraint>(0);
                this.regardSearchStrictConstraints = false;
            }
            else { // the strict version does not hold for /all/
                   // possible values of a_i
                // instead of m_1 + ... + m_n >(=) 0, we can state m'_1 >(=) 0, ..., m'_n >(=) 0
                // where m'_i is like m_i, but with factor and all exponents reduced to 1
                Set<SimplePolynomial> strippedMonomials = inputConstraint.getPolynomial().stripFactorsExponentsAndSums();
                for (SimplePolynomial strippedMonomial : strippedMonomials) {
                    SimplePolyConstraint simplifiedConstraint = new SimplePolyConstraint(strippedMonomial, GE);
                    this.processedSearchStrictConstraints.add(simplifiedConstraint);
                }
            }
        }
        // (2) all addends have negative factors
        //     => all of them are equal to zero, even with their factors and
        //        exponents stripped to one, and inputConstraint can /never/
        //        be oriented strictly, so we can store the result
        //        in this.intermediateConstraints
        else if (inputConstraint.allNegative()) {
            Set<SimplePolyConstraint> resultingConstraints = inputConstraint.addendsToConstraintsForConstantSign();
            if (resultingConstraints == null) {
                // inputConstraint is unsatisfiable
                return false;
            }
            for (SimplePolyConstraint spc : resultingConstraints) {
                if (! this.usefulEQConstraints1.contains(spc)) {
                    this.intermediateConstraints.addLast(spc);
                }
            }
        }
        // (3) inputConstraint consists of two addends where one of them has
        //     a positive factor and the other one is a negative number.
        //     Then each indefinite in the non-empty IndefinitePart must
        //     be greater than zero, regardless of whether inputConstraint
        //     will be oriented strictly later on.
        else {
            BigInteger numericalAddend = inputConstraint.getNumericalAddend();
            if ((numericalAddend.signum() < 0) && (inputConstraint.numberOfAddends() == 2)) {
                Set<SimplePolyConstraint> resultingConstraints;
                resultingConstraints = inputConstraint.getConstraintsAllIndefinitesGT0();
                for (SimplePolyConstraint c : resultingConstraints) {
                    if (! this.usefulGTConstraints.contains(c)) {
                        this.intermediateConstraints.addFirst(c);
                    }
                }
                this.processedSearchStrictConstraints.add(inputConstraint);
            }
            else {
                // (4) nothing can be done
                this.processedSearchStrictConstraints.add(inputConstraint);
            }
        }
        return true;
    }

    /**
     * Performs a simplification of inputConstraint without making use of
     * any other constraints ("context") that might be useful. This is done
     * by analyzing the structure of inputConstraint and making suitable
     * deductions. The resulting useful constraints will be put into
     * this.intermediateConstraints if they have not been seen before.
     * If no simplification is possible or if it is necessary in order not
     * to endanger equivalence between inputConstraint and the resulting
     * constraints, inputConstraint will be placed in
     * this.processedComplexConstraints.
     *
     * this.intermediateConstraints is assumed to be empty when
     * simplifyContextFree is called.
     *
     * @param inputConstraint  to be simplified
     * @return false in case an inconsistency is detected, true otherwise
     */
    private boolean simplifyContextFree (SimplePolyConstraint inputConstraint) {

        if (Globals.useAssertions) {
            assert(this.intermediateConstraints.isEmpty());
        }
        ConstraintType type = inputConstraint.getType();
        if (type == EQ) {

            // 1st step: if all addends have the same sign, each of them
            //           must be equal to zero
            //              => include the addends with factor 1 in
            //                 intermediateConstraints; contradiction if
            //                 an addend is numerical
            if (inputConstraint.allPositive() ||
                inputConstraint.allNegative()) {
                Set<SimplePolyConstraint> newUsefulConstraints = inputConstraint.addendsToConstraintsForConstantSign();
                if (newUsefulConstraints == null) {
                    return false;
                }
                else {
                    for (SimplePolyConstraint newConstraint : newUsefulConstraints) {

                        // add only new constraints
                        if (! this.usefulEQConstraints1.contains(newConstraint)) {
                            this.intermediateConstraints.addLast(newConstraint);
                        }
                    }
                }

            }

            // 2nd step: how many addends?
            // case 0: see 1st step, do nothing
            // case 1: see 1st step, do nothing
            // case 2: if one addend is numerical, then divide by
            //         factor of the other addend (had better be possible w/o
            //         remainder, else: contradiction) and include the result
            //         in intermediateConstraints
            //         else: include the constraint
            //               in processedComplexConstraints
            // default: include the constraint in processedComplexConstraints
            else {
                switch (inputConstraint.numberOfAddends()) {
                case 0: // have already been taken care of
                case 1: // in the 1st step, do not happen
                    if (Globals.useAssertions) {
                        assert false;
                    }
                    break;
                case 2:
                    if (inputConstraint.getNumericalAddend().signum() != 0) {
                        SimplePolyConstraint resultingConstraint = inputConstraint.simplifyConstraintWithANumericalAndAnotherAddend();
                        if (resultingConstraint == null) {
                            return false;
                        }
                        else {
                            if (! this.usefulEQConstraints2.contains(resultingConstraint)) {
                                this.intermediateConstraints.addLast(resultingConstraint);

                                // additionally, we can deduce that all
                                // indefinite coefficients in
                                // resultingConstraint must be > 0
                                for (SimplePolyConstraint newGTConstraint : resultingConstraint.getConstraintsAllIndefinitesGT0()) {
                                    if (! this.usefulGTConstraints.contains(newGTConstraint)) {
                                        this.intermediateConstraints.addFirst(newGTConstraint);
                                    }
                                }
                            }
                        }
                    }
                    else { // inputConstraint has two non-empty IndefiniteParts
                        this.processedComplexConstraints.add(inputConstraint);
                    }
                    break;
                default:
                    this.processedComplexConstraints.add(inputConstraint);
                    break;
                }
            }
        }
        else if (type == GE) {
            // 1) In case all numerical coefficients of the simplePoly are
            //    positive, the constraint is always satisfied and thus
            //    redundant
            //    => no need to include it anywhere
            if (inputConstraint.allPositive() ) {
                ;
            }
            // 2) In case all numerical coefficients are negative,
            //    state equivalently that each IndefinitePart (with
            //    its exponents stripped to one) in inputConstraint
            //    must be equal to zero; get a contradiction in case
            //    an addend has an empty IndefinitePart
            //    (i.e., it is a number != 0)
            else if (inputConstraint.allNegative() ) {
                Set<SimplePolyConstraint> resultingConstraints = inputConstraint.addendsToConstraintsForConstantSign();
                if (resultingConstraints == null) {
                    // inputConstraint is unsatisfiable
                    return false;
                }
                else {
                    for (SimplePolyConstraint newConstraint : resultingConstraints) {
                        if (! this.usefulEQConstraints1.contains(newConstraint)) {
                            this.intermediateConstraints.addLast(newConstraint);
                        }
                    }
                }
            }
            // 3) In case there are two addends of which one is a
            //    negative numerical constant and the other one containing
            //    a positive numerical factor, deduce as additional constraints
            //    to the current one that all non-numerical coefficients that
            //    occur in the IndefinitePart must be > 0.
            else {
                BigInteger numericalAddend = inputConstraint.getNumericalAddend();

                if ((numericalAddend.signum() < 0) &&
                    (inputConstraint.numberOfAddends() == 2)) {
                    // (note that the factor of the IndefinitePart being
                    // positive is the case because otherwise 2) would have
                    // matched already)

                    // instead of e.g. 2*a_8 - 6 >= 0, write a_8 - 3 >= 0.
                    inputConstraint = inputConstraint.simplifyConstraintWithANumericalAndAnotherAddend();

                    if (Globals.useAssertions) {
                        assert (inputConstraint != null);
                    }

                    Set<SimplePolyConstraint> resultingConstraints = inputConstraint.getConstraintsAllIndefinitesGT0();

                    for (SimplePolyConstraint newConstraint : resultingConstraints) {
                        if (! this.usefulGTConstraints.contains(newConstraint)) {
                            // add a_i > 0 for all a_i in the nonempty
                            // IndefinitePart, useful for further deduction
                            this.intermediateConstraints.addFirst(newConstraint);
                        }
                    }

                    if (! numericalAddend.equals(BigInteger.valueOf(-1))) {
                        this.processedComplexConstraints.add(inputConstraint);
                        // otherwise equivalence is not assured any more
                    }
                    // else:
                    //      b*indefinitePart - 1 >= 0
                    // <=>  indefinitePart > 0
                    // <=>  all a_i > 0
                    //   hence: inputConstraint can be omitted
                }
                // 4) If all addends commonly contain a_1^l_1 * ... * a_n^l_n
                //    as factors, we can divide each addend by
                //    a_1^(l_1 - 1) * ... * a_n^(l_n - 1), thus obtaining an
                //    equivalent constraint.
                /*
                else {
                    IndefinitePart commonFactor = inputConstraint.computeCommonFactorsPowersMinusOne();
                    if (! commonFactor.isEmpty()) {
                        // commonFactor contains some a_i
                        SimplePolynomial simplePoly = inputConstraint.divide(commonFactor);
                        processedComplexConstraints.add( new SimplePolyConstraint(simplePoly, GE) );
                    }
                */
                    // 5) nothing at all could be done with inputConstraint
                    else {
                        this.processedComplexConstraints.add(inputConstraint);
                    }
                //}
            }
        }
        return true; // no inconsistencies found
    }

    /* Methods for /context-sensitive/ simplification. */

    /**
     * Given usefulConstraint, we can first simplify it using
     * this.usefulGTConstraints and then use the result to
     * eliminate any addends that are multiples of the result
     * (which is constrained to be equal to zero) in any constraint.
     *
     * It is assumed that there are no GT constraints (of type GE)
     * present in this.intermediateConstraints when this method
     * is called. (This is likely to be the case because exactly
     * the useful constraints of type GE are supposed to be
     * inserted at the head of this.intermediateConstraints.)
     *
     * This method should only be called with a constraint that
     * matches a_i * ... * a_k = 0.
     *
     * @param usefulConstraint  constraint of type EQ which must
     *  have exactly one addend on its LHS
     * @return false in case an inconsistency is detected, true otherwise
     */
    private boolean simplifyEQ1(SimplePolyConstraint usefulConstraint, Abortion aborter) throws AbortionException {

        aborter.checkAbortion();

        if (Globals.useAssertions) {
            assert(usefulConstraint.getType() == EQ);
            assert(usefulConstraint.numberOfAddends() == 1);
            assert(!usefulConstraint.getPolynomial().getIndefiniteParts().contains(IndefinitePart.ONE));
            for (SimplePolyConstraint intermediateConstraint : this.intermediateConstraints) {
                assert(intermediateConstraint.getType() == EQ);
            }
        }

        // Remove unneeded indefinite factors using usefulGTConstraints
        // (those that are known to be > 0 cannot contribute to the
        // product of the indefinites being = 0).
        Set<String> superfluousIndefinites = new LinkedHashSet<String>();
        for (SimplePolyConstraint usefulGTConstraint : this.usefulGTConstraints) {
            superfluousIndefinites.addAll(usefulGTConstraint.getIndefinites());
        }
        SimplePolyConstraint simplifiedUsefulConstraint;
        simplifiedUsefulConstraint = usefulConstraint.removeIndefinitesEfficiently(superfluousIndefinites);
        // we'll work with the simplified version

        if ((! this.usefulEQConstraints1.contains(simplifiedUsefulConstraint)) &&
            (! this.intermediateConstraints.contains(simplifiedUsefulConstraint))) {
            if (simplifiedUsefulConstraint.getNumericalAddend().signum() != 0) {
                return false; // constraint c = 0 for c != 0 is inconsistent
            }
            else {
                Set<String> indefinitesZero = simplifiedUsefulConstraint.getIndefinites();
                // the indefinites whose product is zero
                // according to simplifiedUsefulConstraint

                // Now eliminate all addends which are multiples of
                // the LHS of simplifiedUsefulConstraint. Do this for all
                // the sets/lists in which they might occur.

                // - usefulEQConstraints1
                // Here, we can eliminate the constraints altogether
                // without losing equivalence if we can simplify them
                // using simplifiedUsefulConstraint
                // (e.g. a simplifiedUsefulConstraint a1*a2 = 0
                // is more useful than a usefulEQConstraint1 a1*a2*a3 = 0,
                // which is a multiple of a1*a2 = 0)
                Iterator<SimplePolyConstraint> usefulEQ1Iter = this.usefulEQConstraints1.iterator();
                while (usefulEQ1Iter.hasNext()) {
                    SimplePolyConstraint oldUsefulEQ1Constraint = usefulEQ1Iter.next();
                    SimplePolyConstraint newUsefulEQ1Constraint;
                    newUsefulEQ1Constraint = oldUsefulEQ1Constraint.eliminateAddendsThatContainAll(indefinitesZero, aborter);
                    if (newUsefulEQ1Constraint.numberOfAddends() == 0) { // simplification successful
                        usefulEQ1Iter.remove();
                    }
                }

                // - intermediateConstraints
                // Distinguish the three cases:
                //   * intermediate constraints of type GE are assumed not to
                //     occur there now
                //   * intermediate constraints of type EQ with 1 addend will
                //     be treated as above
                //   * intermediate constraints of type EQ with 2 addends can
                //     be ignored as well because being able to simplify them
                //     would indicate an inconsistency, and it would have been
                //     found already due to the associated constraints of type
                //     GE that are assumed to have already been processed until
                //     now.
                ListIterator<SimplePolyConstraint> intermediateIter = this.intermediateConstraints.listIterator(0);
                while (intermediateIter.hasNext()) {
                    SimplePolyConstraint oldIntermediateConstraint = intermediateIter.next();
                    if (Globals.useAssertions) {
                        assert oldIntermediateConstraint.getType() == EQ;
                    }
                    // TODO remove the EQ condition in the following expression
                    if (oldIntermediateConstraint.getType() == EQ &&
                        (oldIntermediateConstraint.numberOfAddends() == 1)) {
                        SimplePolyConstraint newIntermediateConstraint;
                        newIntermediateConstraint = oldIntermediateConstraint.eliminateAddendsThatContainAll(indefinitesZero, aborter);
                        if (newIntermediateConstraint.numberOfAddends() == 0) { // simplification successful
                            intermediateIter.remove();
                        }
                    }
                }

                // - complexConstraints
                this.applyEQ1OnMany(indefinitesZero, this.complexConstraints,
                        this.complexConstraints, true, aborter);

                // - processedComplexConstraints
                this.applyEQ1OnMany(indefinitesZero, this.processedComplexConstraints,
                        this.complexConstraints, true, aborter);

                if (this.regardSearchStrictConstraints) {
                    // - this.searchStrictConstraints
                    this.applyEQ1OnMany(indefinitesZero, this.searchStrictConstraints,
                            this.searchStrictConstraints, false, aborter);

                    // - this.processedSearchStrictConstraints
                    this.applyEQ1OnMany(indefinitesZero, this.processedSearchStrictConstraints,
                            this.searchStrictConstraints, false, aborter);
                }
            }
            // retire simplifiedUsefulConstraint
            this.usefulEQConstraints1.add(simplifiedUsefulConstraint);

            return true; // no inconsistency found
        }
        else { // we've seen simplifiedConstraint already
            return true;
        }
    }

    /**
     * Helper method for simplifyEQ1.
     *
     * @param indefinitesZero  the product of these indefinites
     *  is known to amount to 0, hence all addends in from that
     *  contain all of them are to be removed
     * @param from  the constraints from <code>from</code>
     *  are to be simplified
     * @param to  the simplified constraints will be stored here
     *  (from == to is allowed)
     * @param checkForBeingKnown  should the new constraint only
     *  be added in case it does not already occur in one of the
     *  containers of regular constraints?
     */
    private void applyEQ1OnMany(Set<String> indefinitesZero,
            Collection<SimplePolyConstraint> from,
            Collection<SimplePolyConstraint> to, boolean checkForBeingKnown,
            Abortion aborter) throws AbortionException {
        List<SimplePolyConstraint> newConstraints;
        newConstraints = new ArrayList<SimplePolyConstraint>();
        // store the new constraints (necessary to add them only after
        // the iteration because from == to is allowed)

        Iterator<SimplePolyConstraint> fromIter = from.iterator();
        while (fromIter.hasNext()) {
            SimplePolyConstraint oldSpc = fromIter.next();
            SimplePolyConstraint newSpc = oldSpc.eliminateAddendsThatContainAll(indefinitesZero, aborter);
            if (! newSpc.equals(oldSpc)) {
                fromIter.remove();

                // regular constraints need not be stored again if known,
                // but in case of searchstrict constraints, we have to be
                // more careful
                if (! checkForBeingKnown || ! this.hasBeenProcessed(newSpc)) {
                    newConstraints.add(newSpc);
                }
            }
        }
        to.addAll(newConstraints);
    }



    /**
     * Given usefulConstraint, simplifyEQ2 replaces any occurrence
     * of a_i^l_i * ... * a_k^l_k by c (except in usefulConstraint,
     * evidently).
     *
     * @param usefulConstraint  has to be of type EQ and of form
     *  a_i^l_i * ... * a_k^l_k - c = 0 with c \in N
     * @return false in case an inconsistency is detected, true otherwise
     */
    private boolean simplifyEQ2(SimplePolyConstraint usefulConstraint) {
        if (Globals.useAssertions) {
            assert(usefulConstraint.getType() == EQ);
            assert(usefulConstraint.numberOfAddends() == 2);
            assert(usefulConstraint.getNumericalAddend().signum() != 0);
            for (IndefinitePart iPart : usefulConstraint.getPolynomial().getIndefiniteParts()) {
                if (! iPart.isEmpty()) {
                    assert(usefulConstraint.getPolynomial().getFactor(iPart).equals(BigInteger.ONE));
                }
            }
        }

        // for all constraints in:
        // EQ2 constraints in intermediate constraints,
        // usefulEQConstraints2, complexConstraints and
        // processedComplexConstraints:
        // * use SimplePolynomial.substitute via a suitable wrapper in
        //   SimplePolyConstraint in order to substitute the non-numerical
        //   addend of usefulConstraint by the negation of the
        //   numerical one
        // * for the members of the former two sets:
        //      > additionally divide by the resulting numerical factor
        //        of the resulting simplified constraint

        // - intermediateConstraints
        ListIterator<SimplePolyConstraint> intermediateIter = this.intermediateConstraints.listIterator(0);
        while (intermediateIter.hasNext()) {
            SimplePolyConstraint oldIntermediateConstraint = intermediateIter.next();

            // Only the intermediate constraints with two addends are to
            // be simplified by simplifyEQ2 because
            // - intermediate GT constraints cannot be simplified like that
            // - intermediate EQ constraints with one addend will be simplified
            //   in the next iterations of simplify() by the new GT constraints
            if (oldIntermediateConstraint.getType().equals(EQ) &&
                (oldIntermediateConstraint.numberOfAddends() == 2)) {

                SimplePolyConstraint newIntermediateConstraint = oldIntermediateConstraint.applyEQ2(usefulConstraint);

                if (! newIntermediateConstraint.equals(oldIntermediateConstraint)) {
                    // Some simplification has taken place.

                    // consistency check (necessary because e.g.
                    // oldIntermediateConstraint == (a_8 - 1 = 0) and
                    // usefulConstraint == (a_8 - 2 = 0) is possible)
                    if (Globals.useAssertions) {
                        // otherwise some constraint has occurred at the same
                        // time both in this.intermediateConstraints and in
                        // an equivalent form in this.usefulEQConstraints2
                        assert (newIntermediateConstraint.numberOfAddends() != 0);
                    }
                    if (newIntermediateConstraint.numberOfAddends() < 2) {
                        return false;
                    }

                    // Unless we have performed a replacement by one,
                    // we have got an undesired numerical factor
                    // in front of the non-empty IndefinitePart of
                    // newIntermediateConstraint. Try to get rid of it.
                    newIntermediateConstraint = newIntermediateConstraint.simplifyConstraintWithANumericalAndAnotherAddend();
                    if (newIntermediateConstraint == null) {
                        return false;
                    }
                    else if (this.usefulEQConstraints2.contains(newIntermediateConstraint) ||
                             this.intermediateConstraints.contains(newIntermediateConstraint)) {
                        // new constraint known by the simplifier => remove the old one
                        intermediateIter.remove();
                    }
                    else { // replace it
                        intermediateIter.set(newIntermediateConstraint);
                    }
                }
            }
        }

        // similar procedure for usefulEQConstraints2, but possibly found
        // simplified constraints will be moved to this.intermediateConstraints
        Iterator<SimplePolyConstraint> usefulEQ2Iter = this.usefulEQConstraints2.iterator();
        while (usefulEQ2Iter.hasNext()) {
            SimplePolyConstraint oldEQ2Constraint = usefulEQ2Iter.next();
            SimplePolyConstraint newEQ2Constraint = oldEQ2Constraint.applyEQ2(usefulConstraint);
            if (! newEQ2Constraint.equals(oldEQ2Constraint)) {
                // Some simplification has taken place.

                // consistency check (necessary because e.g.
                // oldIntermediateConstraint == (a_8 - 1 = 0) and
                // usefulConstraint == (a_8 - 2 = 0) is possible)
                if (newEQ2Constraint.numberOfAddends() < 2) {
                    return false;
                }

                // Now, unless we have performed a replacement by one,
                // we have got an undesired numerical factor
                // in front of the non-empty IndefinitePart of
                // newEQ2Constraint. Try to get rid of it.
                newEQ2Constraint = newEQ2Constraint.simplifyConstraintWithANumericalAndAnotherAddend();
                if (newEQ2Constraint == null) {
                    return false;
                }
                else {
                    // remove the old one from usefulEQ2Constraints;
                    // add the new one to intermediateConstraints
                    // only if it really is new to the simplifier
                    usefulEQ2Iter.remove();
                    if ((! this.usefulEQConstraints2.contains(newEQ2Constraint)) &&
                        (! this.intermediateConstraints.contains(newEQ2Constraint))) {
                        this.intermediateConstraints.addLast(newEQ2Constraint);
                    }
                }
            }
        }

        // Now to complexConstraints and processedComplexConstraints:
        // In both cases, the simplification result should be put into
        // complexConstraints.
        this.applyEQ2OnMany(usefulConstraint, this.complexConstraints,
                this.complexConstraints, true);

        this.applyEQ2OnMany(usefulConstraint, this.processedComplexConstraints,
                this.complexConstraints, true);

        if (this.regardSearchStrictConstraints) {
            // Last, but not least, perform the substitution on
            // this.searchStrictConstraints and this.processedSearchStrictConstraints.
            this.applyEQ2OnMany(usefulConstraint, this.searchStrictConstraints,
                    this.searchStrictConstraints, false);
            this.applyEQ2OnMany(usefulConstraint, this.processedSearchStrictConstraints,
                    this.searchStrictConstraints, false);
        }
        // retire usefulConstraint
        this.usefulEQConstraints2.add(usefulConstraint);
        return true;
    }

    /**
     * Helper method for simplifyEQ2.
     *
     * @param eq2  has to be of type EQ and of form
     *  a_i^l_i * ... * a_k^l_k - c = 0 with c \in N
     * @param from  the constraints from <code>from</code>
     *  are to be simplified
     * @param to  the simplified constraints will be stored here
     *  (from == to is allowed)
     * @param checkForBeingKnown  should the new constraint only
     *  be added in case it does not already occur in one of the
     *  containers of regular constraints?
     */
    private void applyEQ2OnMany(SimplePolyConstraint eq2,
            Collection<SimplePolyConstraint> from,
            Collection<SimplePolyConstraint> to, boolean checkForBeingKnown) {
        List<SimplePolyConstraint> newConstraints;
        newConstraints = new ArrayList<SimplePolyConstraint>();
        // store the new constraints (necessary to add them only after
        // the iteration because from == to is allowed)

        Iterator<SimplePolyConstraint> fromIter = from.iterator();
        while (fromIter.hasNext()) {
            SimplePolyConstraint oldSpc = fromIter.next();
            SimplePolyConstraint newSpc = oldSpc.applyEQ2(eq2);
            if (! newSpc.equals(oldSpc)) {
                fromIter.remove();

                // regular constraints need not be stored again if known,
                // but in case of searchstrict constraints, we have to be
                // more careful
                if (! checkForBeingKnown || ! this.hasBeenProcessed(newSpc)) {
                    newConstraints.add(newSpc);
                }
            }
        }
        to.addAll(newConstraints);
    }


    /**
     * Given usefulConstraint, simplifyGT eliminates all occurrences
     * of the indefinite contained in usefulConstraint in the useful
     * constraints a_i * ... * a_k = 0.
     *
     * Should only be called with a constraint that matches a_i - 1 >= 0.
     *
     * @param usefulConstraint  constraint of type GE
     *  which must match a_i - 1 >= 0.
     * @return false in case an inconsistency is detected, true otherwise
     */
    private boolean simplifyGT(SimplePolyConstraint usefulConstraint) {


        if (Globals.useAssertions) {
            assert(usefulConstraint.getType() == GE);
            assert(usefulConstraint.numberOfAddends() == 2);
            assert(usefulConstraint.getIndefinites().size() == 1);
            SimplePolynomial poly = usefulConstraint.getPolynomial();
            Set<IndefinitePart> indefiniteParts = poly.getIndefiniteParts();
            assert(indefiniteParts.contains(IndefinitePart.ONE));
            for (IndefinitePart iPart : indefiniteParts) {
                if (iPart.isEmpty()) {
                    assert(poly.getFactor(iPart).equals(BigInteger.valueOf(-1)));
                }
                else {
                    assert(poly.getFactor(iPart).equals(BigInteger.ONE));
                }
            }
        }
        // the indefinites of usefulConstraints
        Set<String> newIndefinites = usefulConstraint.getIndefinites();

        // we need to check all places where a_i * ... * a_k = 0
        // are likely to be found:
        // intermediateConstraints and usefulEQConstraints1

        // regarding intermediateConstraints:
        ListIterator<SimplePolyConstraint> intermediateIter = this.intermediateConstraints.listIterator(0);
        while (intermediateIter.hasNext()) {

            // the intermediate constraint before simplification
            SimplePolyConstraint oldIntermediate = intermediateIter.next();
            if (oldIntermediate.getType() == EQ &&
                (oldIntermediate.numberOfAddends() == 1)) {

                // Can we simplify intermediate with usefulConstraint?
                // If so, we should do it and update intermediate
                // to its simplified version.

                // simplified version of oldIntermediate
                SimplePolyConstraint newIntermediate;
                newIntermediate = oldIntermediate.removeIndefinitesEfficiently(newIndefinites);

                if (! newIntermediate.equals(oldIntermediate)) {
                    if (newIntermediate.getNumericalAddend().signum() != 0) {
                        return false; // constraint c = 0 for c != 0 is inconsistent
                    }
                    else {
                        // remove oldIntermediate if its simplified version is known,
                        // update it only if the newIntermediate really is new
                        if (this.usefulEQConstraints1.contains(newIntermediate) ||
                            this.intermediateConstraints.contains(newIntermediate)) {
                            intermediateIter.remove();
                        }
                        else {
                            intermediateIter.set(newIntermediate);
                        }
                    }
                }
            }
        }

        // now regarding usefulEQConstraints1:
        Iterator<SimplePolyConstraint> eq1Iter = this.usefulEQConstraints1.iterator();
        while (eq1Iter.hasNext()) {
            SimplePolyConstraint oldEQConstraint = eq1Iter.next();
            // can be simplified (perhaps)

            SimplePolyConstraint newEQConstraint;
            // simplified version of oldEQConstraint

            newEQConstraint = oldEQConstraint.removeIndefinitesEfficiently(newIndefinites);

            if (! newEQConstraint.equals(oldEQConstraint)) {
                if (newEQConstraint.getNumericalAddend().signum() != 0) {
                    return false; // constraint c = 0 for c != 0 is inconsistent
                }
                else {

                    // remove oldEQConstraint and add its simplified version
                    // newEQConstraint to intermediateConstraints if new,
                    // it might be applicable
                    eq1Iter.remove();

                    if ( (! this.usefulEQConstraints1.contains(newEQConstraint)) &&
                         (! this.intermediateConstraints.contains(newEQConstraint))) {
                        // only add it if it has not occurred before
                        this.intermediateConstraints.addLast(newEQConstraint);
                    }
                }
            }
        }

        // retire usefulConstraint
        this.usefulGTConstraints.add(usefulConstraint);
        return true;
    }


    /* Up to here, none of the (non-constructor-)methods except simplify()
       have used this.valueMap or this.refMap. */

    /**
     * Checks for all constraints a_i - 1 >= 0
     * in this.usefulGTConstraints whether their respective
     * indefinite a_i occurs in this.processedComplexConstraints,
     * this.usefulEQConstraints1 or this.usefulEQConstraints2 and,
     * should this not be the case, removes it, introducing an
     * entry a_i |-> 1 into this.valueMap. If a_i occurs as a key
     * in this.refMap, the elements of the corresponding value will
     * also be mapped to 1 in this.valueMap, and the corresponding
     * entry in this.refMap will be removed.
     *
     * Goal: Reduce the search space for the polynomial interpretation.
     *
     * To be called only after all the other simplifications
     * have been performed.
     */
    private void simplifyGTsWhoseIndefiniteOccursNowhereElse() {

        if (Globals.useAssertions) {
            assert this.complexConstraints.isEmpty();
            assert this.searchStrictConstraints.isEmpty();
            assert this.intermediateConstraints.isEmpty();
        }

        // TODO maybe collect all the gtIndefinites first and then get the
        // indefinites of the other collections just once, removing them
        // from the set of getIndefinites while it is not empty yet;
        // survivors can then safely be set to 1
        Iterator<SimplePolyConstraint> gtIter = this.usefulGTConstraints.iterator();
        outerLoop : while(gtIter.hasNext()) {
            SimplePolyConstraint gtConstraint = gtIter.next();
            String gtIndefinite = null;
            for (String gtIndef : gtConstraint.getIndefinites()) {
                // there should be exactly one
                gtIndefinite = gtIndef;
            }

            if (Globals.useAssertions) {
                assert gtConstraint.getIndefinites().size() == 1;
                for (SimplePolyConstraint constraint : this.usefulEQConstraints1) {
                    assert(! constraint.getIndefinites().contains(gtIndefinite));
                    // if this assertion fails, we are not done simplifying
                    // using GT constraints!
                }
            }
            for (SimplePolyConstraint constraint : this.usefulEQConstraints2) {
                if (constraint.getIndefinites().contains(gtIndefinite)) {
                    continue outerLoop;
                }
            }
            for (SimplePolyConstraint constraint : this.processedComplexConstraints) {
                if (constraint.getIndefinites().contains(gtIndefinite)) {
                    continue outerLoop;
                }
            }
            for (SimplePolyConstraint c : this.processedSearchStrictConstraints) {
                if (c.getIndefinites().contains(gtIndefinite)) {
                    continue outerLoop;
                }
            }

            // We have not been diverted by a continue statement
            // -> replace gtConstraint
            if (Globals.useAssertions) {
                assert(! this.valueMap.containsKey(gtIndefinite));
                for (Set<String> values : this.refMap.values()) {
                    assert(! values.contains(gtIndefinite));
                }
            }

            if (false && Globals.DEBUG_FUHS) {
                System.err.println(gtIndefinite + " ONLY SEEMS TO OCCUR IN (" +
                        gtIndefinite + " > 0) => SET TO 1!");
            }

            this.valueMap.put(gtIndefinite, BigInteger.ONE);

            Set<String> refSet = this.refMap.get(gtIndefinite);
            if (refSet != null) {
                for (String referredTo : refSet) {
                    this.valueMap.put(referredTo, BigInteger.ONE);
                }
                this.refMap.remove(gtIndefinite);
            }

            gtIter.remove();
        }
    }


    /**
     * @param constraint to be checked for containment in one of the containers
     *  of constraints used for storing processed non-searchStrict-constraints
     *  in some way
     * @return whether constraint occurs in one of the containers of this whose
     *  contents have already been processed in some way (i.e., all container
     *  attributes of this except this.complexConstraints)
     */
    private boolean hasBeenProcessed(SimplePolyConstraint constraint) {
        return (this.processedComplexConstraints.contains(constraint) ||
                this.usefulGTConstraints.contains(constraint) ||
                this.usefulEQConstraints1.contains(constraint) ||
                this.usefulEQConstraints2.contains(constraint) ||
                this.intermediateConstraints.contains(constraint));
    }


    /* methods for using this.graph */

    /**
     * Initializes this.graph with the numerical nodes  [0 .. this.range]
     * and the corresponding edges.
     */
    private void initGraph() {
        this.graph = new Graph<GENode, Object>();
        this.numericalNodeCache = new GENode[this.maxRange.intValue() + 1];

        // first create all the numerical nodes
        for (BigInteger i = BigInteger.ZERO;
             i.compareTo(this.maxRange) <= 0;
             i = i.add(BigInteger.ONE)) {
            GENode numericalGENode = GENode.create(i);
            this.numericalNodeCache[i.intValue()] = numericalGENode;
            Node<GENode> numericalNode = this.toNode(numericalGENode);
            this.graph.addNode(numericalNode);
        }

        // then add the corresponding strict > edges
        for (Node<GENode> node1 : this.graph.getNodes()) {
            if (Globals.useAssertions) {
                assert node1.getObject().isNumerical();
            }
            BigInteger n1 = node1.getObject().number;
            for (Node<GENode> node2 : this.graph.getNodes()) {
                BigInteger n2 = node2.getObject().number;
                if (n1.compareTo(n2) > 0) {
                    this.graph.addEdge(node1, node2);
                }
            }
        }
    }


    /**
     * Analyzing the constraints, build the graph which contains the
     * corresponding indefinites and numbers as nodes.
     * Numbers will be added
     *   a) if they occur in [0 .. this.range]  or
     *   b) if they occur in some SPC
     *
     * Reflexive edges are only included from 0 to 0 and from this.range to
     * this.range as of now because they do not contribute anything to
     * finding SCCs with more than one element.
     *
     * @return whether the constraints are possibly satisfiable over
     *  {0, ..., this.range}
     */
    private boolean buildGraph() {
        // iterate over all constraints
        for (SimplePolyConstraint spc : this.usefulEQConstraints1) {
            if (! this.analyzedSPCsForGraph.contains(spc)) {
                Pair<GENode, GENode> eqPair = spc.getPolynomial().toGENodePair();
                if (eqPair != null) {
                    // spc is of type EQ => corresponding edges symmetric
                    Node<GENode> node1, node2;
                    node1 = this.toNode(eqPair.x);
                    node2 = this.toNode(eqPair.y);
                    if (node2 == null) {
                        return false;
                    }
                    else {
                        this.graph.addEdge(node1, node2);
                        this.graph.addEdge(node2, node1);
                    }
                }
                this.analyzedSPCsForGraph.add(spc);
            }
        }

        for (SimplePolyConstraint spc : this.usefulEQConstraints2) {
            if (! this.analyzedSPCsForGraph.contains(spc)) {
                Pair<GENode, GENode> eqPair = spc.getPolynomial().toGENodePair();
                if (eqPair != null) {
                    // spc is of type EQ => corresponding edges symmetric
                    Node<GENode> node1, node2;
                    node1 = this.toNode(eqPair.x);
                    node2 = this.toNode(eqPair.y);
                    if (node2 == null) {
                        return false;
                    }
                    else {
                        this.graph.addEdge(node1, node2);
                        this.graph.addEdge(node2, node1);
                    }
                }
                this.analyzedSPCsForGraph.add(spc);
            }
        }

        for (SimplePolyConstraint spc : this.usefulGTConstraints) {
            if (! this.analyzedSPCsForGraph.contains(spc)) {
                Pair<GENode, GENode> gePair = spc.getPolynomial().toGENodePair();
                if (gePair != null) {
                    // spc is of type GE => corresponding edges are just unidirectional
                    Node<GENode> node1, node2;
                    node1 = this.toNode(gePair.x);
                    node2 = this.toNode(gePair.y);
                    if (node2 == null) {
                        return false;
                    }
                    else {
                        this.graph.addEdge(node1, node2);
                    }
                }
                this.analyzedSPCsForGraph.add(spc);
            }
        }

        for (SimplePolyConstraint spc : this.processedComplexConstraints) {
            if (! this.analyzedSPCsForGraph.contains(spc)) {
                if (spc.numberOfAddends() == 2) {
                    if (spc.getType() == EQ) {
                        Pair<GENode, GENode> eqPair = spc.getPolynomial().toGENodePair();
                        if (eqPair != null) {
                            Node<GENode> node1, node2;
                            node1 = this.toNode(eqPair.x);
                            node2 = this.toNode(eqPair.y);
                            if (node2 == null) {
                                return false;
                            }
                            else {
                                this.graph.addEdge(node1, node2);
                                this.graph.addEdge(node2, node1);
                            }
                        }
                    }
                    else { // type GE
                        if (Globals.useAssertions) {
                            assert(spc.getType() == GE);
                        }

                        Pair<GENode, GENode> gePair = spc.getPolynomial().toGENodePair();
                        if (gePair != null) {
                            Node<GENode> node1, node2;
                            node1 = this.toNode(gePair.x);
                            node2 = this.toNode(gePair.y);
                            if (node2 == null) {
                                return false;
                            }
                            else {
                                this.graph.addEdge(node1, node2);
                            }
                        }
                    }
                }
                this.analyzedSPCsForGraph.add(spc);
            }
        }

        // in case we obtain a cycle due to some
        // processedSearchStrictConstraint, it would not have been orientable
        // strictly anyway
        if (this.regardSearchStrictConstraints) {
            for (SimplePolyConstraint spc : this.processedSearchStrictConstraints) {
                if (! this.analyzedSPCsForGraph.contains(spc)) {
                    if (spc.numberOfAddends() == 2) {
                        Pair<GENode, GENode> gePair = spc.getPolynomial().toGENodePair();
                        if (gePair != null) {
                            Node<GENode> node1, node2;
                            node1 = this.toNode(gePair.x);
                            node2 = this.toNode(gePair.y);
                            if (node2 == null) {
                                return false;
                            }
                            else {
                                this.graph.addEdge(node1, node2);
                            }
                        }
                    }
                    this.analyzedSPCsForGraph.add(spc);
                }
            }
        }

        // now create the edges wrt the indefs and their respective ranges
        GENode lowerBoundGENode = this.numericalNodeCache[0];
        Node<GENode> lowerBoundNode = this.graph.getNodeFromObject(lowerBoundGENode);
        for (Node<GENode> currentNode : this.graph.getNodes()) {
            if (! currentNode.getObject().isNumerical()) {
                String indef = currentNode.getObject().indefinite;
                BigInteger indefRange = this.ranges.get(indef);
                GENode upperBoundGENode = this.numericalNodeCache[indefRange.intValue()];
                Node<GENode> upperBoundNode = this.graph.getNodeFromObject(upperBoundGENode);
                this.graph.addEdge(upperBoundNode, currentNode);
                this.graph.addEdge(currentNode, lowerBoundNode);
            }
        }
        return true;
    }

    /**
     * Given a GENode, check whether we already know the corresponding Node
     * in this.graph. If so, return it, otherwise create a new Node which
     * encapsulates the GENode.
     *
     * @param geNode to be encapsulated in a -- preferably known (by
     *  this.graph) -- Node
     * @return null if geNode is numerical and represents a number which
     *  is greater than this.range or smaller than 0, the Node in which geNode
     *  is encapsulated in this.graph if such a Node exists, a new Node
     *  which encapsulates geNode otherwise
     */
    private Node<GENode> toNode(GENode geNode) {
        if (geNode.isNumerical() &&
            ((geNode.number.compareTo(this.maxRange) > 0) || (geNode.number.signum() < 0))) {
            return null;
        }
        Node<GENode> result = this.graph.getNodeFromObject(geNode);
        if (result == null) {
            result = new Node<GENode>(geNode);
        }
        return result;
    }


    /**
     * Transfers knowledge from this.graph to this.refMap and this.valueMap.
     * Collapses SCCs of this.graph to be just one node of the corresponding
     * SCC afterwards, preferably with a numerical label if possible.
     * Indefinites which correspond to nodes in this.graph will be
     * substituted according to the maps in the constraints stored in this.
     * Simplifies the SimplePolyConstraints of this using this knowledge.
     *
     * @return (false, false) in case an inconsistency is detected (if this occurs,
     *                        the specialization will probably have been performed
     *                        only incompletely)
     *         (true, true) in case no inconsistency is detected and a simplification
     *                      inside some SimplePolyConstraint of this has been performed
     *         (true, false) in case no inconsistency is detected and no simplification
     *                       inside (but possibly some removal of) some
     *                       SimplePolyConstraint of this has been performed
     * (possibly satisfiable, some new constraint created via simplification)
     */
    private Pair<Boolean, Boolean> applyGraphSCCs() {
        Set<Cycle<GENode>> sccs = this.graph.getSCCs();

        // map GENodes to the Cycles (SCCs) they are supposed to replace
        Map<GENode, Cycle<GENode>> graphReplacementMap = new LinkedHashMap<GENode, Cycle<GENode>>();

        // map indefinites to numbers/other indefinites by which they are
        // to be substituted in the constraints of this as deduced by
        // the equalities of the SCCs of this.graph
        Map<String, GENode> constraintSpecializationMap = new LinkedHashMap<String, GENode>();

        // DEBUG
        //System.out.println("this.graph before applying SCCs");
        //System.out.println(this.graph);

        for (Cycle<GENode> cycle : sccs) {
            if (cycle.size() > 1) { // else nothing to do

                // DEBUG
                //System.out.println("Current SCC is " + cycle);

                Set<GENode> nodes = cycle.getNodeObjects();

                BigInteger number = null;
                Set<String> indefinites = new LinkedHashSet<String>(cycle.size());

                // Which indefinite shall be the representative one?
                // 1) an arbitrary one
                // 2) the one which is smallest wrt the natural order on String
                // 3) the one which occurs most often
                // 4) the one which occurs in most constraints

                // Take option 1) for now.

                GENode representative = null;
                // element of cycle to which we will rename the other elements
                // of cycle in the SimplePolyConstraints of this; all nodes
                // of cycle will be merged to representative afterwards

                for (GENode node : nodes) {
                    if (node.isNumerical()) {
                        if (number == null) {
                            number = node.number;
                            representative = node;
                        }
                        else {
                            // beware SCCs with two numbers in them,
                            // for they are unsatisfiable
                            return new Pair<Boolean,Boolean>(false,false);
                        }
                    }
                    else {
                        indefinites.add(node.indefinite);
                    }
                }

                // some consistency checks:
                if (Globals.useAssertions) {
                    for (String indefinite : indefinites) {
                        // * valueMap must not know any of indefinites
                        assert(! this.valueMap.keySet().contains(indefinite));
                        // * refMap must not know members of indefinites as
                        //   values
                        for (Set<String> values : this.refMap.values()) {
                            assert(! values.contains(indefinite));
                        }
                    }
                    // * valueMap.values() must be a subset of
                    //   {0, ..., this.range}
                    for (BigInteger numValue : this.valueMap.values()) {
                        assert(numValue.signum() >= 0);
                        assert(numValue.compareTo(this.maxRange) <= 0);
                    }
                    // * all entries of refMap have disjoint values,
                    //   and there must not be any indefinite that
                    //   is both a key and an element of some value
                    for (Entry<String, Set<String>> entry1 : this.refMap.entrySet()) {
                        String key1 = entry1.getKey();
                        Set<String> value1 = entry1.getValue();
                        assert(! value1.contains(key1));
                        for (Entry<String, Set<String>> entry2 : this.refMap.entrySet()) {
                            String key2 = entry2.getKey();
                            Set<String> value2 = entry2.getValue();
                            if (! key1.equals(key2)) {
                                assert (! value2.contains(key1));
                                for (String someValue : value1) {
                                    assert(! value2.contains(someValue));
                                }
                            }
                        }
                    }
                    // * refMap and valueMap shall not contain any indefinite
                    //   twice, regardless of how this came to happen
                    for (String valueMapKey : this.valueMap.keySet()) {
                        assert(! this.refMap.containsKey(valueMapKey));
                        for (Set<String> refSet : this.refMap.values()) {
                            assert(! refSet.contains(valueMapKey));
                        }
                    }
                }

                // if number != null:
                // - map all of indefinites to number
                // - if refMap contains any a_i of indefinites
                //   as key, move the key and all elements of its value to
                //   valueMap, map them to number;
                if (number != null) {
                    for (String indefinite : indefinites) {
                        this.valueMap.put(indefinite, number);
                        Set<String> refSet = this.refMap.get(indefinite);
                        if (refSet != null) {
                            // indefinite occurs as key in refMap
                            for (String referredTo : refSet) {
                                this.valueMap.put(referredTo, number);
                            }
                            this.refMap.remove(indefinite);
                        }
                    }
                }
                else {
                    // so, number == null:
                    // (1) assert there is no a_i in the scc that is also
                    //     in a *value* of refMap!  -> all values of refMap
                    //     should either have been eliminated from the graph
                    //     or occur in another of the current SCCs
                    //
                    // (2) check whether \exists a_i in indefinites
                    //     that is a key of refMap and if so, map all the other
                    //     indefinites there, but be careful: there might be
                    //     more than one such a_i; in such a case, we should
                    //     just unite the corresponding values and remove these
                    //     entries from refMap
                    //
                    // (3) if there is no a_i in indefinites that is a key of
                    //     refMap, pick some a_i in indefinites, map it to the
                    //     rest of indefinites in refMap and substitute all
                    //     the other a_j from indefinites by a_i in all the
                    //     constraints of this.
                    if (Globals.useAssertions) {
                        // if number has not been set so far, then neither
                        // should representative
                        assert representative == null;

                        // (1)
                        for (Set<String> refSet : this.refMap.values()) {
                            assert Collections.disjoint(refSet, indefinites);
                        }
                    }

                    Iterator<String> indefsIter = indefinites.iterator();
                    while (indefsIter.hasNext()) {
                        String indefinite = indefsIter.next();
                        if (Globals.useAssertions) {
                            // indefinite must not occur in this.valueMap because
                            // all the indefinites from this.valueMap should have
                            // been eliminated from the constraints in this
                            // and hence also from the graph
                            assert (! this.valueMap.containsKey(indefinite));
                        }
                        // try refMap (2)
                        Set<String> refSet = this.refMap.get(indefinite);
                        if (refSet != null) {
                            // add all elements of the current cycle but the
                            // future representative
                            refSet.addAll(indefinites);
                            refSet.remove(indefinite);
                            representative = GENode.create(indefinite);

                            // now be careful: another element of indefinites
                            // might also be a key of refMap; note that we
                            // only have to consider the remaining indefinites
                            // of indefsIter because indefinite is the first
                            // such indefinite in refMap ("first" w.r.t. the
                            // order of the iteration)
                            while (indefsIter.hasNext()) {
                                String keyCandidate = indefsIter.next();
                                Set<String> moreIndefinites = this.refMap.get(keyCandidate);
                                if (moreIndefinites != null) {
                                    refSet.addAll(moreIndefinites);
                                    this.refMap.remove(keyCandidate);
                                }
                            }
                            break;
                        }
                    }
                    if (representative == null) { // (3)
                        representative = GENode.create(indefinites.iterator().next());
                        indefinites.remove(representative.indefinite);
                        this.refMap.put(representative.indefinite, indefinites);
                    }
                }

                if (Globals.useAssertions) {
                    assert(representative != null);
                }

                // store information needed for modifying the graph
                graphReplacementMap.put(representative, cycle);

                // get the information needed for updating the constraints of this
                // using the equalities implied by cycle
                for (GENode node : nodes) {
                    if (! node.equals(representative)) {
                        if (Globals.useAssertions) {
                            assert(! node.isNumerical());
                        }
                        constraintSpecializationMap.put(node.indefinite, representative);
                    }
                }
            }
        }

        // Having updated the maps, we can now proceed to modify the graph:
        // Merge all the nodes of cycle into one.
        for (Map.Entry<GENode, Cycle<GENode>> entry : graphReplacementMap.entrySet()) {
            final GENode representative = entry.getKey();
            this.graph.merge(entry.getValue(), new BinaryOperation<GENode>() {
                @Override
                public GENode combine(GENode one, GENode two) {
                    return representative;
                }
            }, null);

            // DEBUG
            //System.out.println("After merging SCC");
            //System.out.println(this.graph);
            //System.out.println("this.valueMap: " + this.valueMap);
            //System.out.println("this.refMap: " + this.refMap);
        }

        // now simplify the constraints of this (keep track of whether
        // an actual modification to a non-trivial constraint takes place,
        // which would indicate that another SimplePolyConstraint-based
        // simplification was in place)

        boolean constraintSimplified = false;
        boolean satisfiable = true; // are the resulting constraints satisfiable?
                                    // (in case of doubt, assume so)
        if (! constraintSpecializationMap.isEmpty()) {
            if (Globals.useAssertions) {
                assert(this.complexConstraints.isEmpty());
                if (this.regardSearchStrictConstraints) {
                    assert(this.searchStrictConstraints.isEmpty());
                }
                assert(this.intermediateConstraints.isEmpty());
            }

            // non-strict eval: like this, we only specialize while it makes sense to do so
            satisfiable = satisfiable && this.substituteInConstraintSet(this.usefulEQConstraints1, constraintSpecializationMap);
            satisfiable = satisfiable && this.substituteInConstraintSet(this.usefulEQConstraints2, constraintSpecializationMap);
            satisfiable = satisfiable && this.substituteInConstraintSet(this.usefulGTConstraints, constraintSpecializationMap);
            satisfiable = satisfiable && this.substituteInConstraintSet(this.processedComplexConstraints, constraintSpecializationMap);
            if (this.regardSearchStrictConstraints) {
                satisfiable = satisfiable && this.substituteInProcessedSearchStrictConstraints(constraintSpecializationMap);
            }

            constraintSimplified = (! this.complexConstraints.isEmpty()) ||
                                (this.regardSearchStrictConstraints &&
                                 ! this.searchStrictConstraints.isEmpty());
        }
        if (satisfiable) {
            return new Pair<Boolean, Boolean>(true, constraintSimplified);
        }
        else {
            return new Pair<Boolean, Boolean>(false, false);
        }
    }


    /**
     * Specializes in constraints using constraintSpecializationMap.
     * Specialized constraints will be removed from constraints
     * and stored in this.complexConstraints.
     *
     * @param constraints its contents are to be specialized;
     *  if some constraint is changed due to specialization, it is
     *  removed from constraints and added to this.complexConstraints.
     * @param constraintSpecializationMap specialization, maps old indefinites
     *  to their replacements
     * @return false if some inconsistent constraint has been generated, true
     *  otherwise; if false is returned, the specialization might not be carried
     *  out completely (because it would be pointless)
     */
    private boolean substituteInConstraintSet(Set<SimplePolyConstraint> constraints,
                                              Map<String, GENode> constraintSpecializationMap) {
        Iterator<SimplePolyConstraint> iter;
        iter = constraints.iterator();
        while (iter.hasNext()) {
            SimplePolyConstraint oldSpc = iter.next();
            SimplePolyConstraint newSpc = oldSpc.specializeGENode(constraintSpecializationMap);
            if (! newSpc.equals(oldSpc)) {

                // DEBUG
                //System.out.println("Specialized " + oldSpc + " to " + newSpc);

                if (! newSpc.isValid()) { // don't add superfluous constraints
                    if (newSpc.isSatisfiable()) {
                        this.complexConstraints.add(newSpc);
                    }
                    else { // give up
                        return false;
                    }
                }
                iter.remove();
            }
        }
        return true;
    }

    /**
     * Specializes in this.searchStrictConstraints
     * using constraintSpecializationMap.
     *
     * @param constraintSpecializationMap specialization, maps old indefinites
     *  to their replacements
     * @return false if some inconsistent constraint has been generated, true
     *  otherwise; if false is returned, the specialization might not be carried
     *  out completely (because it would be pointless)
     */
    private boolean substituteInProcessedSearchStrictConstraints(Map<String, GENode> constraintSpecializationMap) {
        Iterator<SimplePolyConstraint> iter;
        iter = this.processedSearchStrictConstraints.iterator();
        while (iter.hasNext()) {
            SimplePolyConstraint oldSpc = iter.next();
            SimplePolyConstraint newSpc = oldSpc.specializeGENode(constraintSpecializationMap);
            if (! newSpc.equals(oldSpc)) {
                // no validity check here, valid constraints are candidates
                // for strict orientation and thus still needed
                if (newSpc.isSatisfiable()) {
                    this.searchStrictConstraints.add(newSpc);
                    iter.remove();
                }
                else {
                    return false;
                }
            }
        }
        return true;
    }
}

