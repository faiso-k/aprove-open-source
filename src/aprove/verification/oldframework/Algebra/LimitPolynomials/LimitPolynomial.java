package aprove.verification.oldframework.Algebra.LimitPolynomials;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;



/**
 * LimitPolynomials are of the form sp_1*X^i_1 + sp_2*X^i_2 + ...
 * where X is a symbol representing a monotonic sequence with infinite limit.
 * The exponents of X are unknown but bounded at interpretation time.
 * A LimitPolynomial is Immutable.
 * @author kabasci
 *
 */
public class LimitPolynomial {

    // A LimitPolynomial is characterized by a number of fields:
    // Its maximum exponent of X, which for sake of speed is stored separately
    // and a collection of LimitMonomials.
    private final int maxExponent;

    private final ImmutableArrayList<LimitMonomial> coeffs;

    public static Logger log = Logger.getLogger("LimitPolynomial");


    public static LimitPolynomial MINUS_ONE = new LimitPolynomial(0, ImmutableCreator.create(new ArrayList(Collections.singleton(new LimitMonomial(SimplePolynomial.ZERO, SimplePolynomial.MINUS_ONE,0)))));
    public static LimitPolynomial ONE = new LimitPolynomial(0, ImmutableCreator.create(new ArrayList(Collections.singleton(new LimitMonomial(SimplePolynomial.ZERO, SimplePolynomial.ONE,0)))));
    public static LimitPolynomial ZERO = new LimitPolynomial(0, ImmutableCreator.create(new ArrayList(Collections.singleton(new LimitMonomial(SimplePolynomial.ZERO, SimplePolynomial.ZERO,0)))));
    public static LimitPolynomial X = new LimitPolynomial(0, ImmutableCreator.create(new ArrayList(Collections.singleton(new LimitMonomial(SimplePolynomial.ONE, SimplePolynomial.ONE,1)))));


    /**
     * Creates a LimitPolynomial with a constant value.
     * @param constant Integer constant
     * @return The created LimitPolynomial.
     */
    public static LimitPolynomial create(BigInteger constant) {
        return new LimitPolynomial(0, ImmutableCreator.create(new ArrayList(Collections.singleton(new LimitMonomial(SimplePolynomial.ZERO, SimplePolynomial.create(constant), 0)))));
    }

    /**
     * Creates a LimitPolynomial with a non-exponented simple polynomial value.
     * This is the standard one for constants.
     * @param poly The Simple Polynomial to which the created LimitPolynomial is equivalent
     * @return The created LimitPolynomial.
     */
    public static LimitPolynomial create(SimplePolynomial poly) {
        return new LimitPolynomial(0, ImmutableCreator.create(new ArrayList(Collections.singleton(new LimitMonomial(SimplePolynomial.ZERO, poly, 0)))));
    }

    /**
     * Creates a LimitPolynomial equivalent to X to the power of the provided simple Polynomial
     * @param maxExponent The maximum exponent this can yield
     * @param poly The Simple Polynomial to which the created LimitPolynomial is X^-equivalent
     * @return The created LimitPolynomial.
     */
    public static LimitPolynomial create(int maxExponent, SimplePolynomial poly) {
        return new LimitPolynomial(maxExponent, ImmutableCreator.create(new ArrayList(Collections.singleton(new LimitMonomial(poly, SimplePolynomial.ONE, maxExponent)))));
    }

    /**
     * Creates a LimitPolynomial equivalent to X to the power of the provided exponent, times the provided base
     * This is the standard one for function argument interpretations.
     * @param maxExponent The maximum exponent this can yield
     * @param poly The Simple Polynomial to which the created LimitPolynomial is X^-equivalent
     * @return The created LimitPolynomial.
     */
    public static LimitPolynomial create(int maxExponent, SimplePolynomial exponent, SimplePolynomial base) {
        return new LimitPolynomial(maxExponent, ImmutableCreator.create(new ArrayList(Collections.singleton(new LimitMonomial(exponent, base, maxExponent)))));
    }




    /**
     * New LimitPolynomial given a maximal exponent and a list of exponent-of-X/base polynomials
     * @param maxExponent
     * @param polynomial
     */
    public LimitPolynomial(final int maxExponent, final ImmutableArrayList<LimitMonomial> polynomial) {
        this.maxExponent = maxExponent;
        this.coeffs = polynomial;
    }

    /**
     * adds a list of LimitPolynomials and returns the sum.
     * @param addends
     * @return
     */
    public static LimitPolynomial plus(final List<LimitPolynomial> addends) {

        final ArrayList<Triple<SimplePolynomial, SimplePolynomial, Integer>> resPoly = new ArrayList<Triple<SimplePolynomial,SimplePolynomial, Integer>>();
        final ArrayList<LimitMonomial> boxResPoly = new ArrayList<LimitMonomial>();
        final Map<SimplePolynomial, Triple<SimplePolynomial, SimplePolynomial, Integer>> cache = new LinkedHashMap<SimplePolynomial, Triple<SimplePolynomial, SimplePolynomial, Integer>>();
        int mE = 0;
        for (final LimitPolynomial entry: addends){
            // The maxExponent of the sum is the maximum of the addends.
            if (entry.maxExponent > mE) {
                mE = entry.maxExponent;
            }

            // Put all the addends in a new list, simplifying where possible.
            for (final LimitMonomial coeff: entry.coeffs)  {

                if (cache.get(coeff.getExponent()) != null) {
                    cache.get(coeff.getExponent()).y = cache.get(coeff.getExponent()).y.plus(coeff.getBase());
                    cache.get(coeff.getExponent()).z = (cache.get(coeff.getExponent()).z > coeff.getMaxExponent())? cache.get(coeff.getExponent()).z : coeff.getMaxExponent();
                } else {
                    // Triples are mutable, better copy.
                    final Triple<SimplePolynomial, SimplePolynomial, Integer> p = new Triple<SimplePolynomial, SimplePolynomial, Integer> (coeff.getExponent(), coeff.getBase(), coeff.getMaxExponent());
                    resPoly.add(p);
                    cache.put(coeff.getExponent(), p);
                }

            }


        }
        // Box the result.
        for (Triple<SimplePolynomial, SimplePolynomial, Integer> e: resPoly) {
            boxResPoly.add(new LimitMonomial(e.x, e.y, e.z));
        }
        return new LimitPolynomial(mE, ImmutableCreator.create(boxResPoly));

    }

    /**
     * suubtracts a LimitPolynomials from the current one and returns the difference.
     * Could be implemented as \x, this -> +(this, -1*x), but this would incur an unnessesary deep copy which we want to avoid.
     * @param subtrahend
     * @return
     */
    public LimitPolynomial minus(final LimitPolynomial subtrahend) {

        final ArrayList<Triple<SimplePolynomial, SimplePolynomial, Integer>> resPoly = new ArrayList<Triple<SimplePolynomial,SimplePolynomial, Integer>>();
        final Map<SimplePolynomial, Triple<SimplePolynomial, SimplePolynomial, Integer>> cache = new LinkedHashMap<SimplePolynomial, Triple<SimplePolynomial, SimplePolynomial, Integer>>();
        final ArrayList<LimitMonomial> boxResPoly = new ArrayList<LimitMonomial>();

        int mE;

        // Put all the monomials of the current limitpolynomial in a new list, caching the exponent map.
        for (final LimitMonomial coeff: this.coeffs)  {
            if (cache.get(coeff.getExponent()) != null) {
                // cannot really happen, but cannot hurt either.
                cache.get(coeff.getExponent()).y = cache.get(coeff.getExponent()).y.plus(coeff.getBase());
                cache.get(coeff.getExponent()).z = cache.get(coeff.getExponent()).z > coeff.getMaxExponent()? cache.get(coeff.getExponent()).z: coeff.getMaxExponent();
            } else {
                // Triples are mutable, better deep copy.
                final Triple<SimplePolynomial, SimplePolynomial, Integer> p = new Triple<SimplePolynomial, SimplePolynomial, Integer> (coeff.getExponent(), coeff.getBase(), coeff.getMaxExponent());
                resPoly.add(p);
                cache.put(coeff.getExponent(), p);
            }
        }

        // Now subtract all the monomials from the subtrahend...
         for (final LimitMonomial coeff: subtrahend.coeffs)  {
            if (cache.get(coeff.getExponent()) != null) {
                // exponent present in original one, just subtract the polynomials. Maximum exponent value still is maximum. (Although they should technically be the same)
                cache.get(coeff.getExponent()).y = cache.get(coeff.getExponent()).y.minus(coeff.getBase());
                cache.get(coeff.getExponent()).z = cache.get(coeff.getExponent()).z > coeff.getMaxExponent()? cache.get(coeff.getExponent()).z: coeff.getMaxExponent();

            } else {
                // Triples are mutable, better deep copy. Furthermore multiply by -1.
                final Triple<SimplePolynomial, SimplePolynomial, Integer> p = new Triple<SimplePolynomial, SimplePolynomial, Integer> (coeff.getExponent(), coeff.getBase().times((BigInteger.valueOf(-1))), coeff.getMaxExponent());
                resPoly.add(p);
                cache.put(coeff.getExponent(), p);
            }
        }

        if (this.maxExponent > subtrahend.maxExponent) {
            mE = this.maxExponent;
        } else {
            mE = subtrahend.maxExponent;
        }

        // Box the result.
        for (Triple<SimplePolynomial, SimplePolynomial, Integer> e: resPoly) {
            boxResPoly.add(new LimitMonomial(e.x, e.y, e.z));
        }

        return new LimitPolynomial(mE, ImmutableCreator.create(boxResPoly));

    }


    /**
     * adds a LimitPolynomials to this one and returns the sum. Just sugar.
     * @param addend
     * @return
     */
    public LimitPolynomial plus(final LimitPolynomial addend) {

        final ArrayList<LimitPolynomial> l = new ArrayList<LimitPolynomial>();
        l.add(this);
        l.add(addend);
        return LimitPolynomial.plus(l);

    }


    /**
     * adds a single monomial (in the Limit sense, of X) to this LimitPolynomial and returns the sum.
     * @param addends
     * @return
     */
    public LimitPolynomial plus(final int maxExponent, final SimplePolynomial base, final SimplePolynomial exponent) {

        final ArrayList<Triple<SimplePolynomial, SimplePolynomial, Integer>> resPoly = new ArrayList<Triple<SimplePolynomial,SimplePolynomial, Integer>>();
        final ArrayList<LimitMonomial> boxResPoly = new ArrayList<LimitMonomial>();

        // Put all the current coefficients in a new list, simplifying with the new one if possible.
        // Make a deep copy of the current LimitPolynomial, to be on the safe side.
        for (final LimitMonomial coeff: this.coeffs){

            if ((coeff.getExponent()) == exponent) {
                resPoly.add(new Triple<SimplePolynomial, SimplePolynomial, Integer>(coeff.getExponent(),coeff.getBase().plus(base), maxExponent));
            } else {
                // Triples are mutable, better copy.
                final Triple<SimplePolynomial, SimplePolynomial, Integer> p = new Triple<SimplePolynomial, SimplePolynomial, Integer> (coeff.getExponent(), coeff.getBase(), coeff.getMaxExponent());
                resPoly.add(p);
            }

        }

        int mE;
        if (maxExponent > this.maxExponent) {
            mE = maxExponent;
        } else {
            mE = this.maxExponent;
        }


        // Box the result.
        for (Triple<SimplePolynomial, SimplePolynomial, Integer> e: resPoly) {
            boxResPoly.add(new LimitMonomial(e.x, e.y, e.z));
        }

        return new LimitPolynomial(mE, ImmutableCreator.create(boxResPoly));

    }


    /**
     * Multiplies a LimitPolynomial by another.
     * @param other
     * @return
     */
    public LimitPolynomial times(final LimitPolynomial other) {

        final ArrayList<Triple<SimplePolynomial, SimplePolynomial, Integer>> resPoly = new ArrayList<Triple<SimplePolynomial,SimplePolynomial, Integer>>();
        final ArrayList<LimitMonomial> boxResPoly = new ArrayList<LimitMonomial>();

        for (final LimitMonomial entry: this.coeffs) {
            for (final LimitMonomial entry2: other.coeffs) {
                SimplePolynomial exponent = entry.getExponent();
                SimplePolynomial exponent2 = entry2.getExponent();
                SimplePolynomial base = entry.getBase();
                SimplePolynomial base2 = entry2.getBase();
                int maxExponent2 = entry.getMaxExponent();
                int maxExponent3 = entry2.getMaxExponent();
                resPoly.add(new Triple<SimplePolynomial, SimplePolynomial, Integer>(exponent.plus(exponent2), base.times(base2),maxExponent2 + maxExponent3));
            }
        }

        // Box the result.
        for (Triple<SimplePolynomial, SimplePolynomial, Integer> e: resPoly) {
            boxResPoly.add(new LimitMonomial(e.x, e.y, e.z));
        }

        return new LimitPolynomial(this.maxExponent+ other.maxExponent, ImmutableCreator.create(boxResPoly));

    }


    /**
     * Multiplies a LimitPolynomial by a polynomial factor (base), and an exponent to X (exponent), and returns the result.
     * @param exponent
     * @param base
     * @param maxExponentDelta The maximum increase of the exponent of X due to the factor exponent
     * @return
     */
    public LimitPolynomial multiplyBy(final SimplePolynomial exponent, final SimplePolynomial base, final int maxExponentDelta) {

        final ArrayList<Triple<SimplePolynomial, SimplePolynomial, Integer>> resPoly = new ArrayList<Triple<SimplePolynomial,SimplePolynomial, Integer>>();
        final ArrayList<LimitMonomial> boxResPoly = new ArrayList<LimitMonomial>();

        for (final LimitMonomial entry: this.coeffs) {
            resPoly.add(new Triple<SimplePolynomial, SimplePolynomial, Integer>(entry.getExponent().plus(exponent), entry.getBase().times(base), entry.getMaxExponent() + maxExponentDelta));
        }

        // Box the result.
        for (Triple<SimplePolynomial, SimplePolynomial, Integer> e: resPoly) {
            boxResPoly.add(new LimitMonomial(e.x, e.y, e.z));
        }


        return new LimitPolynomial(this.maxExponent + maxExponentDelta, ImmutableCreator.create(boxResPoly));

    }

    /**
     * Counts the unique Coefficients.
     */
    private static long uid= 0;

    /**
     * Returns a SimplePolynomial coefficient with a unique name tmp_LimitPolynomial_<uid>.
     * Synchronized to avoid race conditions
     * @return
     */
    private synchronized static SimplePolynomial getFreshCoefficient(String descr) {
        return SimplePolynomial.create(descr + Long.toString(LimitPolynomial.uid++));
    }


    /**
     * Converts this LimitPolynomial to a list of constraints.
     * Note that there is a different method for extracting strict components in DP context.
     * @param relation Should this LimitPolynomial be aligned >, >= or =?
     * @return A pair of the list of all constraints needed to satiyfy the relation, and in the >= case additionally a constraint
     *         distinguishing a >=-solution from a >-solution. Is to be called by one of two wrappers below.
     */
    private Pair<List<SimplePolyConstraint>, SimplePolyConstraint> toConstraintsInternal (final ConstraintType relation) {

        // The collected constraints
        final List<SimplePolyConstraint> constraintList = new ArrayList<SimplePolyConstraint>();

        // The condition to be satisfied to distinguish >-Solutions from >=-Solutions. Only applicable for relation==GE
        SimplePolyConstraint strictCond = null;


        // First part:
        // For each monomial, we extract binary variables stating that this monomial has exponent rank x.

        // This stores these variables.
        final Map<Pair<LimitMonomial, Integer>, SimplePolynomial> exponentRanks = new LinkedHashMap<Pair<LimitMonomial, Integer>, SimplePolynomial>();

        List<SimplePolynomial> atLeastOne;

        for (final LimitMonomial coeff: this.coeffs) {
            atLeastOne = new ArrayList<SimplePolynomial>();
            for (int i = 0; i <= coeff.getMaxExponent(); i++) {

                final SimplePolynomial c = LimitPolynomial.getFreshCoefficient("exponent_rank_" + i + "_#");
                // This simple Polynomial shall be bound by 0-1
                constraintList.add(new SimplePolyConstraint(c, ConstraintType.GE));
                constraintList.add(new SimplePolyConstraint(c.times(BigInteger.valueOf(-1)).plus(SimplePolynomial.ONE), ConstraintType.GE));
                // And each exponent needs a value, thus store the indicators.
                atLeastOne.add(c);


                // One could use equality constraints here, however we prefer two constraints, one >= and one <=.
                constraintList.add(new SimplePolyConstraint(coeff.getExponent().minus(SimplePolynomial.create(BigInteger.valueOf(i))).times(c), ConstraintType.GE));
                constraintList.add(new SimplePolyConstraint(coeff.getExponent().minus(SimplePolynomial.create(BigInteger.valueOf(i))).times(c).times(BigInteger.valueOf(-1)), ConstraintType.GE));

                exponentRanks.put(new Pair<LimitMonomial, Integer>(coeff, i), c);

            }
            // At least (and exactly) one exponent should be true. We already ensured in the part above that at most one is true.
            constraintList.add(new SimplePolyConstraint(SimplePolynomial.plus(atLeastOne).minus(SimplePolynomial.ONE), ConstraintType.GE));
        }

        // Next step: Encode indicators that for a given exponent the combined polynomial is in relation.
        // Note that these indicators are only implied, not equivalent to the relation. This is enough.
        // We need to distinguish two cases:
        // For = we only need equivalence of all monomials. There we do not need the indicators.
        // For > or >= we need to lexicographically compare. The difference is whether all >= is accepted or not.
        // Thus we need a second set of indicators for the GEQ-Case.
        final Map<Integer, SimplePolynomial> indicators = new LinkedHashMap<Integer, SimplePolynomial>();
        final Map<Integer, SimplePolynomial> indicatorsGeq = new LinkedHashMap<Integer, SimplePolynomial>();

        for (int i=0; i <= this.maxExponent; i++) {
            List<SimplePolynomial> monomialList = new ArrayList<SimplePolynomial>();
            for (final LimitMonomial coeff: this.coeffs) {
                final Pair<LimitMonomial, Integer> p = new Pair<LimitMonomial, Integer>(coeff, i);
                final SimplePolynomial ind = exponentRanks.get(p);

                // If this does not exist this monomial cannot get as high, ignore it.
                if (ind != null) {
                    monomialList.add(ind.times(coeff.getBase()));
                }

            }



            if (relation == ConstraintType.EQ) {
                // Simply encode the equality.
                final SimplePolynomial sp = SimplePolynomial.plus(monomialList);
                constraintList.add(new SimplePolyConstraint(sp, ConstraintType.EQ));

            } else {
                // Encode the relation coefficient via ind*(sum[indexp(i,c)*pol(c)]) >= and for > as >= ind*1
                final SimplePolynomial cgt = LimitPolynomial.getFreshCoefficient("gt_#");
                // This simple Polynomial shall be bound by 0-1
                constraintList.add(new SimplePolyConstraint(cgt, ConstraintType.GE));
                constraintList.add(new SimplePolyConstraint(cgt.times(BigInteger.valueOf(-1)).plus(SimplePolynomial.ONE), ConstraintType.GE));
                indicators.put(i,cgt);

                final SimplePolynomial cge = LimitPolynomial.getFreshCoefficient("ge_#");
                // This simple Polynomial shall be bound by 0-1
                constraintList.add(new SimplePolyConstraint(cge, ConstraintType.GE));
                constraintList.add(new SimplePolyConstraint(cge.times(BigInteger.valueOf(-1)).plus(SimplePolynomial.ONE), ConstraintType.GE));
                indicatorsGeq.put(i,cge);

                final SimplePolynomial spgt = SimplePolynomial.plus(monomialList).minus(SimplePolynomial.ONE).times(cgt);
                constraintList.add(new SimplePolyConstraint(spgt, ConstraintType.GE));
                final SimplePolynomial spge = SimplePolynomial.plus(monomialList).times(cge);
                constraintList.add(new SimplePolyConstraint(spge, ConstraintType.GE));

            }



        }



        // For equality, we are done.
        // For >= and > we now need to combine the indicators to ensure they lead to a valid combination.
        // This means a lexicographical comparision, since the exponent of X ensures that a higher exponent order-wise beats any smaller one.
        if (relation != ConstraintType.EQ) {

            // in propositional logic we have ind_max v (indge_max^ind_(max-1)) v (indge_max^indge_(max-1)^ind_(max-2)) v ...
            // where for > the last possible disjunct (^(i=1..max)indge_i) is excluded.

            // in polynomials, this can be written by using multiplication instead of conjunction, addition instead of disjunction, and asserting >=1.
            final List<SimplePolynomial> disjuncts = new ArrayList<SimplePolynomial>();
            for (int i=0; i<=this.maxExponent; i++) {
                final List<SimplePolynomial> geMons = new ArrayList<SimplePolynomial>();
                for (int j=i+1; j <= this.maxExponent; j++) {
                    geMons.add(indicatorsGeq.get(j));
                }
                geMons.add(indicators.get(i));
                final SimplePolynomial p = SimplePolynomial.times(geMons);
                disjuncts.add(p);
            }


            // If we have a >=-Relation, the last possible option is that actually all relations are >=.
            if (relation == ConstraintType.GE) {
                List<SimplePolynomial> geMons = new ArrayList<SimplePolynomial>();
                for (int j=0; j <= this.maxExponent; j++) {
                    geMons.add(indicatorsGeq.get(j));
                }
                final SimplePolynomial p = SimplePolynomial.times(geMons);
                disjuncts.add(p);

                geMons = new ArrayList<SimplePolynomial>();
                // Furthermore in the GE-Case, compute the strictness constraint as a sum over all the >-indicators.
                for (int j=0; j <= this.maxExponent; j++) {
                    geMons.add(indicators.get(j));
                }
                final SimplePolynomial strict = SimplePolynomial.plus(geMons);
                strictCond = new SimplePolyConstraint(strict, ConstraintType.GE /* as expected by SATSearch, the real strict condition is GT */);

            }
            // We need to ensure at least one of those conditions is actually fulfilled.
            disjuncts.add(SimplePolynomial.MINUS_ONE);
            constraintList.add(new SimplePolyConstraint(SimplePolynomial.plus(disjuncts), ConstraintType.GE));
        }

        return new Pair<List<SimplePolyConstraint>, SimplePolyConstraint>(constraintList, strictCond);


    }



    /**
     * This is the wrapper of toConstraintsInternal to generate a constraint (as a list of simple polynomial constaints) for any given relation type.
     * @param relation Which order is requested?
     * @return
     */
    public List<SimplePolyConstraint> toConstraints(final ConstraintType relation) {
        return this.toConstraintsInternal(relation).x;
    }


    /**
     * This is the wrapper of toConstraintsInternal for generating a list of GE-Constraints and a searchstrict contraint.
     * @return A pair of the list of all constraints needed to satiyfy the relation, and in the >= case additionally a constraint
     *         distinguishing a >=-solution from a >-solution. Is to be called by one of two wrappers below.
     */
    public Pair<List<SimplePolyConstraint>, SimplePolyConstraint> toConstraints() {
        return this.toConstraintsInternal(ConstraintType.GE);
    }


    /**
     * Specializes a LimitPolynomial after a solution has been found.
     * @param goalState The solution as returned by the search engine
     * @return A LimitPolynomial which has been specialized by the solution
     */
    public LimitPolynomial specialize(final Map<String, BigInteger> goalState) {

        // To simplify the results, we use a map. It is probable that after specialization quite some entries which have been distinct before are equal.
        final Map<SimplePolynomial, SimplePolynomial> resGathered = new LinkedHashMap<SimplePolynomial, SimplePolynomial>();

        for (final LimitMonomial monom: this.coeffs) {
            final SimplePolynomial specExp = monom.getExponent().specialize(goalState);
            if (resGathered.get(specExp) != null) {
                // Already have an entry of that exponent
                resGathered.put(specExp, resGathered.get(specExp).plus(monom.getBase().specialize(goalState)));
            } else {
                // This is the first monomial of that exponent power.
                resGathered.put(specExp, monom.getBase().specialize(goalState));
            }
        }



        // We now use this map to make a list - ImmutableCreator does not let us do that directly, so we need to Iterate.
        final ArrayList<Triple<SimplePolynomial, SimplePolynomial, Integer>> resList = new ArrayList<Triple<SimplePolynomial,SimplePolynomial, Integer>>();
        for (final Map.Entry<SimplePolynomial, SimplePolynomial> entry : resGathered.entrySet()) {
            resList.add(new Triple<SimplePolynomial, SimplePolynomial, Integer> (entry.getKey(), entry.getValue(), entry.getKey().interpret(goalState, BigInteger.ZERO).intValue()));
        }

        ArrayList<LimitMonomial> boxResPoly = new ArrayList<LimitMonomial>();

        // Box the result.
        for (Triple<SimplePolynomial, SimplePolynomial, Integer> e: resList) {
            boxResPoly .add(new LimitMonomial(e.x, e.y, e.z));
        }

        return new LimitPolynomial (this.maxExponent, ImmutableCreator.create(boxResPoly));

    }

    /**
     * Exports a LimitPolynomial for a proof.
     * @param eo The export utility to use
     * @param LimitSymbol The symbol to use for the limit coefficient
     * @return
     */
    public String export(final Export_Util eo, final String LimitSymbol) {

        // We sort the exponents.
        final List<LimitMonomial> l = new ArrayList<LimitMonomial>();
        l.addAll(this.coeffs);
        Collections.sort(l, new LimitMonomial.MonomialComparator());

        final StringBuilder res = new StringBuilder();

        boolean first = true;

        for (final LimitMonomial entry: l) {
            if (!first) {
                res.append(" + ");
            } else {
                first = false;
            }
            res.append(entry.getBase().export(eo));
            res.append(eo.multSign());
            res.append(LimitSymbol);
            res.append(eo.sup(entry.getExponent().export(eo)));
        }
        return res.toString();

    }


    /**
     * Exports a LimitPolynomial for a proof. Wrapper for the one where the Limit symbol is free, this one uses a caligraphic X.
     * @param eo
     * @return
     */
    public String export(final Export_Util eo) {
        return this.export(eo, eo.calligraphic("X"));
    }


    /**
     * Returns true iff a specialized LimitPolynomial is greater than zero in value.
     * @return
     */
    public boolean gtZero() {

        // Sort monomials by exponent.
        final List<LimitMonomial> l = new ArrayList<LimitMonomial>();
        l.addAll(this.coeffs);
        Collections.sort(l, new LimitMonomial.MonomialComparator());

        // compare to zero lexigraphically.
        for (LimitMonomial m: l) {
            // Are we bigger than zero? Then yes. Otherwise carry on.
            // If we are not specialized enough, return false.
            if (!m.getBase().isConstant() | !m.getExponent().isConstant()) {LimitPolynomial.log.log(Level.FINEST, "Could not compare"); return false;}
            // We are greater if lexicographically we are greater in any component and greater than or equal in all higher ones.
            if (m.getBase().getNumericalAddend().compareTo(BigInteger.ZERO) > 0) {return true;}
            if (m.getBase().getNumericalAddend().compareTo(BigInteger.ZERO) < 0) {return false;}

        }
        return false;

    }

    /**
     * Returns true iff a specialized LimitPolynomial is greater than or equal zero in value.
     * @return
     */
    public boolean geZero() {

        // Sort monomials by exponent.
        final List<LimitMonomial> l = new ArrayList<LimitMonomial>();
        l.addAll(this.coeffs);
        Collections.sort(l, new LimitMonomial.MonomialComparator());


        // compare to zero lexigraphically.
        for (LimitMonomial m: l) {
            // Are we bigger than zero? Then yes. Otherwise carry on.
            // If we are not specialized enough, return false.
            if (!m.getBase().isConstant() | !m.getExponent().isConstant()) {LimitPolynomial.log.log(Level.FINEST, "Could not compare"); return false;}
            LimitPolynomial.log.log(Level.FINEST, m.getBase().toString() + "X^" + m.getExponent().toString());
            // We are greater if lexicographically we are greater in any component and greater than or equal in all higher ones.
            if (m.getBase().getNumericalAddend().compareTo(BigInteger.ZERO) > 0) {return true;}
            if (m.getBase().getNumericalAddend().compareTo(BigInteger.ZERO) < 0) {return false;}

        }
        // Only difference to gt: for ge >= 0 in all components is perfectly ok.
        return true;

    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        for (int i =0; i < this.coeffs.size(); i++) {
            if (i > 0 ) {
                sb.append(" + ");
            }
            sb.append(this.coeffs.get(i).toString());
        }

        return sb.toString();

    }


}
