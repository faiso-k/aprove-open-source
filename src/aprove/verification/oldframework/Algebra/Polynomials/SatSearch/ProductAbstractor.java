package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Performs product abstraction for SimplePolyConstraints.
 *
 * This class has been inspired by the parts of FDConstraints that are used to
 * perform product abstraction on SimplePolyConstraints.
 *
 * TODO update docs
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class ProductAbstractor {

    // for our new indefinites that represent abstracted products
    private static final String PREFIX = "c_";
    private int nextIndex = 1;

    private Set<String> forbiddenNames;

    public ProductAbstractor(Set<String> forbiddenNames) {
        this.forbiddenNames = forbiddenNames;
    }

    public LinkedHashMap<String, StringPair> abstractProducts(List<SimplePolyConstraint> spcs,
            List<SimplePolyConstraint> moreSpcs,
            Map<String, BigInteger> ranges, BigInteger defaultRange) {
        Map<StringPair, Integer> products;
        products = this.getProducts(spcs, moreSpcs);
        LinkedHashMap<String, StringPair> result;
        result = this.simplify(spcs, moreSpcs, products, ranges, defaultRange);
        if (Globals.useAssertions) {
            for (int i : products.values()) {
                assert i == 0 || i == 1;
            }
        }
        return result;
    }

    /**
     * Heavily based on FDConstraints.simplify().
     *
     * Copied and pasted docu-guess (fuhs): (TODO write up-to-date docs!)
     * Simplifies constraints by introducing new EQ
     * SimplePolyConstraints of type a_i * a_j - a_k = 0 into
     * additionalConstraints for constraints like ... a_i^m * a_j^(m-n) * ... >=
     * or = 0, replacing a_i^m*a_j^(m-n) by a_i^n * a_k^(m-n) in the process.
     * This is done until there are no products with more than two factors left.
     *
     * fuhs (much later):
     * I think that it is done until no product occurs more than once.
     * Maybe we should keep going until there are no products whatsoever
     * in order to make multiplication order clear.
     *
     * @param constraints
     *            the SimplePolyConstraints to be simplified; will be modified
     *            to contain the simplified SPCs afterwards
     * @param products
     *            mapping [StringPair -> Integer], keeps track of how many times
     *            a given product of variables occurs
     * @param bits
     *            how long is the bit vector that is used for the indefinite?
     *            -> will be updated inside the method!
     * @param forbiddenNames
     *            Set of Strings which must not be used for new coefficients
     * @return mapping of indefinites that stand for abstracted products to the
     *         product they abstract.
     *         The map entries are ordered in such a way that any element of
     *         a key is either an indefinite that either has already occurred
     *         in the original constraints or has occurred as a value of the
     *         map earlier.
     */
    private LinkedHashMap<String, StringPair> simplify(List<SimplePolyConstraint> constraints,
            List<SimplePolyConstraint> moreConstraints,
            Map<StringPair, Integer> products,
            Map<String, BigInteger> origRanges, BigInteger defaultRange) {

        // do not insert the abstracted vars into the original ranges,
        // the latter might be needed as such later on; we also need to
        // use BigInteger to prevent overflows
        DefaultValueMap<String, BigInteger> ranges;
        ranges = new DefaultValueMap<String, BigInteger>(defaultRange);
        ranges.putAll(origRanges);

        // to which product does the new indefinite correspond?
        LinkedHashMap<String, StringPair> indefsToProducts;
        indefsToProducts = new LinkedHashMap<String, StringPair>(128);

        StringPair pair;
        // product of two indefinites (i.e., Diophantine variables)

        do {
            // We need to find the next product to abstract.

            // In contrast to FDSearch, we also have to regard the number of
            // bits used for the products, so the number of occurrences does
            // not suffice as a weight for the product; instead, consider the
            // number of occurrences times the product of the ranges of the
            // indefinites.

            // Note that abstracting from "expensive" products is preferable
            // over abstracting from "cheap" ones!
            int maxWeight = 0;
            pair = null;
            for (Entry<StringPair, Integer> entry : products.entrySet()) {
                int count = entry.getValue();
                if (count > 0) {
                    // Note that in FDSearch, it said "count > 1" here!
                    // Here, however, we get rid of them all.
                    StringPair key = entry.getKey();
                    int weightOfOneProduct;
                    if (key.one.equals(key.two)) {
                        // squares are preferred over non-squares-products
                        // since their circuits are smaller
                        // -> double weight
                        BigInteger range = ranges.get(key.one);
                        int length = range.bitLength();
                        weightOfOneProduct = length * length * 2; //range * range * 2;
                    }
                    else {
                        BigInteger range1 = ranges.get(key.one);
                        BigInteger range2 = ranges.get(key.two);
                        int length1 = range1.bitLength();
                        int length2 = range2.bitLength();
                        weightOfOneProduct = length1 * length2;
                    }

                    int currentWeight = weightOfOneProduct * count;
                    if (currentWeight > maxWeight) {
                        maxWeight = currentWeight;
                        pair = key;
                    }
                }
            }
            if (pair != null) {
                String newIndefinite = this.nextName();
                BigInteger range1 = ranges.get(pair.one);
                BigInteger range2 = ranges.get(pair.two);
                ranges.put(newIndefinite, range1.multiply(range2));
                products.remove(pair);
                if (!pair.one.equals(pair.two)) {
                    this.replaceProducts(constraints, pair, newIndefinite, products);
                    this.replaceProducts(moreConstraints, pair, newIndefinite, products);
                }
                else {
                    this.replaceSquares(constraints, pair, newIndefinite, products);
                    this.replaceSquares(moreConstraints, pair, newIndefinite, products);
                }

                if (Globals.useAssertions) {
                    assert ! indefsToProducts.containsKey(newIndefinite);
                }
                indefsToProducts.put(newIndefinite, pair);
            }
        } while (pair != null);

        return indefsToProducts;
    }

    /**
     * docu-guess (fuhs): Counts how many times a product a_i * a_j or a_i^2
     * occurs in this.
     *
     * @param spcs
     *            one of the Lists of SimplePolyConstraints for which the
     *            occurrences of the products are to be counted
     * @param moreSpcs
     *            one of the Lists of SimplePolyConstraints for which the
     *            occurrences of the products are to be counted
     * @return mapping [StringPair -> Integer] which keeps track of how many
     *         times a product of two variables (stored in the key of the
     *         mapping) has been observed.
     */
    private Map<StringPair, Integer> getProducts(Collection<SimplePolyConstraint> spcs,
            Collection<SimplePolyConstraint> moreSpcs) {
        Map<StringPair, Integer> products = new LinkedHashMap<StringPair, Integer>();
        for (SimplePolyConstraint c : spcs) {
            c.getPolynomial().getProducts(products);
        }
        for (SimplePolyConstraint c : moreSpcs) {
            c.getPolynomial().getProducts(products);
        }
        return products;
    }

    /**
     * docu-guess (fuhs): Replaces all products with factors pair by z in
     * constraints. Modifies products accordingly.
     *
     * @param constraints
     *            products are to be replaced here
     * @param pair
     *            the two factors of the product which is to be replaced;
     *            assumed not to occur in products any more
     * @param z
     *            replacement for pair.one * pair.two
     * @param products
     *            keeps track of how often each product of two variables occurs
     *            in the system (map StringPair -> Integer), is modified to suit
     *            the changes in this
     */
    private void replaceProducts(List<SimplePolyConstraint> constraints,
            StringPair pair, String z, Map<StringPair, Integer> products) {
        ListIterator<SimplePolyConstraint> iter = constraints.listIterator();
        while (iter.hasNext()) {
            SimplePolyConstraint c = iter.next();
            iter.set(new SimplePolyConstraint(c.getPolynomial().replaceProducts(pair.one, pair.two, z, products), c.getType()));
        }
    }

    /**
     * docu-guess (fuhs): Replaces (pair.one)^2 by z in this where pair.one
     * occurs at a power > 2. products is modified accordingly in the process.
     *
     * @param constraints
     *            products are to be replaced here
     * @param pair
     *            (pair.one)^2 is to be replaced in this where pair.one occurs
     *            at power > 2; assumed not to occur in products any more
     * @param z
     *            replacement for (pair.one)^2
     * @param products
     *            keeps track of how often each product of two variables occurs
     *            in the system (map StringPair -> Integer), is modified to suit
     *            the changes in this
     */
    private void replaceSquares(List<SimplePolyConstraint> constraints,
            StringPair pair, String z, Map<StringPair, Integer> products) {
        ListIterator<SimplePolyConstraint> iter = constraints.listIterator();
        while (iter.hasNext()) {
            SimplePolyConstraint c = iter.next();
            iter.set(new SimplePolyConstraint(c.getPolynomial().replaceSquares(pair.one, z, products), c.getType()));
        }
    }


    /**
     * @return a fresh Diophantine variable
     */
    private String nextName() {
        String result;
        do {
            result = ProductAbstractor.PREFIX + this.nextIndex;
            ++this.nextIndex;
        } while (this.forbiddenNames.contains(result));
        return result;
    }
}
