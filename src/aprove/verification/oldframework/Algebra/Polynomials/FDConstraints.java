package aprove.verification.oldframework.Algebra.Polynomials;


import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 *
 * docu-guess (fuhs):
 * Contains a list of FiniteDomains and information derived from them regarding
 * the ranges over which they are to be solved, the FiniteDomains in which
 * the indefinites occur on the rhs and the total number of those occurrences.
 */
public class FDConstraints {


  // some docu-guesses given behind declarations (thiemann)
  public final List<FiniteDomain> constraints;
  private int currentIndex; // fuhs guesses: the index of the FiniteDomain that will be added next to constraints
  public final Map<String, Set<Integer>> dpg;  // which fd-constraints depend on that variable
    // (indefinite coefficient actually, but the comments and identifiers in this
    // and other classes related to finite domain search nonetheless
    // often call them "variables")

  public final SortedMap<String, Integer> occ; // how often does a variable occur in fd-constraints (number occurences or number constraints?) (fuhs guesses: number of total occurrences)
  public BigInteger range; // maximal range over which the values for some coefficient are to be found
  public final Map<String, BigInteger> ranges; // coefficient -> maxRange (String -> Int)

  private Abortion aborter;

  public final List<Map<Integer, Boolean>> searchStrictFDs;
  // searchStrictFDs contains mappings from indices of
  // FiniteDomains that are exactly those that correspond to
  // some common searchStrict SimplePolyConstraint to whether
  // the *lower* boundary of the corresponding FiniteDomain
  // is to be modified when making them strict.

    /**
     * docu-guess (fuhs):
     * @param aborter Abortion to be used
     * @param constraints Set of SimplePolyConstraints to be processed
     * @param searchStrictConstraints the searchStrictConstraints to be
     *  processed (GE, one of them is supposed be oriented strictly)
     * @param range integer solutions for the coefficients of constraints
     *  will be sought in [0, range]
     *
     */
  private FDConstraints(Abortion aborter, Set<SimplePolyConstraint> constraints,
                        Set<SimplePolyConstraint> searchStrictConstraints,
                        BigInteger range) throws
      UnsolveableConstraintException, AbortionException {
    this.aborter = aborter;
    this.constraints = new ArrayList<FiniteDomain>(128);
    this.currentIndex = 0;
    this.dpg = new HashMap<String, Set<Integer>>(100);
    this.occ = new TreeMap<String, Integer>(new Comparator<String>() {
      @Override
    public int compare(String o1, String o2) {
        return o2.compareTo(o1);
      }
    });
    this.searchStrictFDs = new ArrayList<Map<Integer, Boolean>>(searchStrictConstraints.size());
    this.range = range;
    this.ranges = new HashMap<String, BigInteger>(100);

    List<SimplePolyConstraint> cs, searchStrictCs;
    cs = new ArrayList<SimplePolyConstraint>(constraints.size());
    searchStrictCs = new ArrayList<SimplePolyConstraint>(searchStrictConstraints.size());

    // collect variables (indefinite coefficients, actually) and transform constraints
    Set<String> variables = new LinkedHashSet<String>();

    // first get vars of the non-searchStrict constraints
    for (SimplePolyConstraint c : constraints) {
      Set<String> vars = c.getPolynomial().getIndefinites();
      if (vars.isEmpty()) {
          if (c.isValid()) {
            continue;
        }
          if (!c.isSatisfiable()) {
              throw new UnsolveableConstraintException(c);
          }
          throw new RuntimeException("a poly constraint without vars should be valid or unsatisfiable!");
      }
      else {
          variables.addAll(vars);
      }
      cs.add(c);
    }

    // then get vars of the searchStrict constraints
    for (SimplePolyConstraint c : searchStrictConstraints) {
        searchStrictCs.add(c);
        Set<String> vars = c.getPolynomial().getIndefinites();
        if (vars.isEmpty()) {
            if (c.isValid()) {
                continue;
            }
            if (!c.isSatisfiable()) {
                throw new UnsolveableConstraintException(c);
            }
            throw new RuntimeException("a poly constraint without vars should be valid or unsatisfiable!");
        }
        else {
            variables.addAll(vars);
        }
    }

    // set initial ranges
    for (String variable : variables) {
      this.ranges.put(variable, this.range);
    }

    Map<StringPair, Integer> products = this.getProducts(cs, searchStrictCs);
    // count product occurrences a_i*a_j in this

    List<SimplePolynomial> additionalConstraints = new LinkedList<SimplePolynomial>();

    this.simplify(cs, searchStrictCs, additionalConstraints, products, variables);
    this.translate(cs, searchStrictCs, additionalConstraints);
  }

  public static FDConstraints create(Abortion aborter, Set<SimplePolyConstraint> constraints,
          Set<SimplePolyConstraint> searchStrictConstraints, BigInteger range)
      throws UnsolveableConstraintException, AbortionException {
    return new FDConstraints(aborter, constraints, searchStrictConstraints, range);
  }


  public void addConstraint(FiniteDomain fd) {
    // add constraint to list
    this.constraints.add(fd);

    // update occurrences table and dependency graph
    this.addOcc(fd.variable, 1);
    for (Entry<String, Integer> e : fd.lowerBound.variables.entrySet()) {
      String variable = e.getKey();
      this.addDep(variable, this.currentIndex);
      this.addOcc(variable, e.getValue());
    }

    for (Entry<String, Integer> e : fd.upperBound.variables.entrySet()) {
      String variable = e.getKey();
      this.addDep(variable, this.currentIndex);
      this.addOcc(variable, e.getValue());
    }

    ++this.currentIndex;
  }

  /**
   * Adds a set of FiniteDomains to this. If searchStrict == true, also
   * adds the index set that corresponds to them in this.constraints to
   * this.searchStrictFDs
   *
   * @param fds the finiteDomains to be added to this
   * @param searchStrict whether these finiteDomains are equivalent to
   *  some searchstrict SimplePolyConstraint (in that case,
   *  this.searchStrictFDs will be modified accordingly)
   */
  public void addConstraints(Map<FiniteDomain, Boolean> fds, boolean searchStrict) {
      if (searchStrict) {
          Map<Integer, Boolean> newSearchStrictIndices;
          // the positions that the keys of fds take in this.constraints
          newSearchStrictIndices = new LinkedHashMap<Integer, Boolean>(fds.size());
          for (Map.Entry<FiniteDomain, Boolean> e : fds.entrySet()) {
              FiniteDomain fd = e.getKey();
              Boolean changeLowerBound = e.getValue();
              newSearchStrictIndices.put(this.currentIndex, changeLowerBound);
              this.addConstraint(fd); // also increments this.currentIndex
          }
          this.searchStrictFDs.add(newSearchStrictIndices);
      }
      else {
          for (Map.Entry<FiniteDomain, Boolean> e : fds.entrySet()) {
              FiniteDomain fd = e.getKey();
              this.addConstraint(fd);
          }
      }
  }


    /**
     * docu-guess (fuhs):
     * Adds the constraint at position index to the set of constraints
     * which depend on variable (in this.dpg).
     * @param variable
     * @param index
     */
  private void addDep(String variable, int index) {
    Set<Integer> cs = this.dpg.get(variable);
    if (cs == null) {
      cs = new LinkedHashSet<Integer>();
      cs.add(index);
      this.dpg.put(variable, cs);
    } else {
        cs.add(index);
    }
  }

    /**
     * docu-guess (fuhs):
     * Increases the count of variable in this.occ (number of occurrences
     * of variable in the system) by count.
     * @param variable
     * @param count
     */
  private void addOcc(String variable, int count) {
    Integer c = this.occ.get(variable);
    if (c == null) {
        this.occ.put(variable, count);
    } else {
        this.occ.put(variable, c + count);
    }
  }

    /**
     * docu-guess (fuhs):
     * Counts how many times a product a_i * a_j or a_i^2 occurs in
     * this.
     *
     * @param constraints1  one of the Lists of SimplePolyConstraints
     *  for which the occurrences of the products are to be counted
     * @param constraints2  the other of the Lists of SimplePolyConstraints
     *  for which the occurrences of the products are to be counted
     * @return mapping [StringPair -> Integer] which keeps
     *  track of how many times a product of two variables (stored in
     *  the key of the mapping) has been observed. Note that the second
     *  variable of a StringPair is never smaller than the first one
     *  with respect to the natural order of String.
     */
  private Map<StringPair, Integer> getProducts(List<SimplePolyConstraint> constraints1,
                                               List<SimplePolyConstraint> constraints2) {
    Map<StringPair, Integer> products = new TreeMap<StringPair, Integer>();
    for (SimplePolyConstraint c : constraints1) {
      c.getPolynomial().getProducts(products);
    }
    for (SimplePolyConstraint c : constraints2) {
        c.getPolynomial().getProducts(products);
    }

    return products;
  }

    /**
     * docu-guess (fuhs):
     * Replaces all products with factors pair by z in constraints.
     * Modifies products accordingly.
     *
     * @param constraints products are to be replaced here
     * @param pair the two factors of the product which is to be replaced;
     *  assumed not to occur in products any more
     * @param z replacement for pair.one * pair.two
     * @param products keeps track of how often each product of two variables
     *  occurs in the system (map StringPair -> Integer), is modified to suit
     *  the changes in this
     */
  private void replaceProducts(List<SimplePolyConstraint> constraints,
                               StringPair pair, String z,
                               Map<StringPair, Integer> products) {
    for (ListIterator<SimplePolyConstraint> iter = constraints.listIterator(); iter.hasNext();) {
      SimplePolyConstraint c = iter.next();
      iter.set( new SimplePolyConstraint(c.getPolynomial().replaceProducts(pair.one, pair.two, z, products),
                                         c.getType()));
    }
  }

    /**
     * docu-guess (fuhs):
     * Replaces (pair.one)^2 by z in this where pair.one occurs at a power > 2.
     * products is modified accordingly in the process.
     *
     * @param constraints products are to be replaced here
     * @param pair (pair.one)^2 is to be replaced in this where pair.one occurs
     *  at power > 2; assumed not to occur in products any more
     * @param z replacement for (pair.one)^2
     * @param products keeps track of how often each product of two variables
     *  occurs in the system (map StringPair -> Integer), is modified to suit
     *  the changes in this
     */
  private void replaceSquares(List<SimplePolyConstraint> constraints,
                              StringPair pair, String z,
                              Map<StringPair, Integer> products) {
    for (ListIterator<SimplePolyConstraint> iter = constraints.listIterator(); iter.hasNext();) {
      SimplePolyConstraint c = iter.next();
      iter.set( new SimplePolyConstraint(c.getPolynomial().replaceSquares(pair.one, z, products),
                                         c.getType()));
    }
  }

    /**
     * docu-guess (fuhs):
     * Simplifies constraints by introducing new EQ SimplePolyConstraints
     * of type a_i * a_j - a_k = 0 into additionalConstraints
     * for constraints like ... a_i^m * a_j^(m-n) * ... >= or = 0,
     * replacing a_i^m*a_j^(m-n) by a_i^n * a_k^(m-n) in the process.
     * This is done until there are no products with more than two
     * factors left.
     *
     * @param constraints the SimplePolyConstraints to be simplified
     * @param sStrictConstraints the searchStrict constraints to be simplified
     * @param additionalConstraints output: will store the additional
     *  constraints of type a_i * a_j - a_k = 0 as SimplePolynomials which are
     *  implicitly treated as though they were SimplePolyConstraints of type EQ.
     * @param products mapping [StringPair -> Integer], keeps track of how
     *  many times a given product of variables occurs
     * @param forbiddenNames Set of Strings which must not be used for
     *  new coefficients
     */
  private void simplify(List<SimplePolyConstraint> constraints,
                        List<SimplePolyConstraint> sStrictConstraints,
                        List<SimplePolynomial> additionalConstraints,
                        Map<StringPair, Integer> products,
                        Set<String> forbiddenNames) throws AbortionException {
    CoefficientFactory coeffFactory = CoefficientFactory.create(forbiddenNames);

    //DEBUG
    //int passes = 0;
    //END

    StringPair pair;
    do {
        this.aborter.checkAbortion();

      // find max used product
      int max = 1;
      pair = null;
      for (Entry<StringPair, Integer> entry : products.entrySet()) {
        int count = entry.getValue();

        if (count > max) {
          max = count;
          pair = entry.getKey();
        }
      }

      if (pair != null) {
        //DEBUG
        //++passes;
        //END
        String newVariable = coeffFactory.nextName();

        if (!pair.one.equals(pair.two)) {
          //DEBUG
          /*System.out.println(
            "Ersetze  "
              + pair.one
              + "*"
              + pair.two
              + "  durch  "
              + newVariable
              + "("
              + max
              + " Mal");*/
          // END

          products.remove(pair);
          this.replaceProducts(constraints, pair, newVariable, products);
          this.replaceProducts(sStrictConstraints, pair, newVariable, products);

          BigInteger newRange = this.ranges.get(pair.one).multiply(this.ranges.get(pair.two));
          this.ranges.put(newVariable, newRange);
          if (newRange.compareTo(this.range) > 0) {
            this.range = newRange;
        }

        } else {
          //DEBUG
          //System.out.println(
           // "Ersetze  " + pair.one + "^2  durch  " + newVariable + "(" + max + " Mal");
          // END

          products.remove(pair);
          this.replaceSquares(constraints, pair, newVariable, products);
          this.replaceSquares(sStrictConstraints, pair, newVariable, products);

          BigInteger newRange = this.ranges.get(pair.one);
          newRange = newRange.pow(2);
          this.ranges.put(newVariable, newRange);
          if (newRange.compareTo(this.range) > 0) {
            this.range = newRange;
        }
        }

        SimplePolynomial x = SimplePolynomial.create(pair.one);
        SimplePolynomial y = SimplePolynomial.create(pair.two);
        SimplePolynomial z = SimplePolynomial.create(newVariable);

        additionalConstraints.add(x.times(y).minus(z));
      }

    } while (pair != null);

    // DEBUG
    /*
    System.out.println("Finished after " + passes + " iterations");
    for (Iterator iter = constraints.iterator(); iter.hasNext();)
      System.out.println(iter.next());
    System.out.println();
    for (Iterator iter = this.ranges.entrySet().iterator(); iter.hasNext();) {
      Entry entry = (Entry) iter.next();
      System.out.println(entry.getKey() + " = " + entry.getValue());
    }
    */
    // END

    if (Globals.useAssertions) {
        for (int i : products.values()) {
            assert i == 0 || i == 1;
        }
    }
  }


    /**
     * docu-guess (fuhs):
     * Translates constraints and additionalConstraints to FiniteDomains
     * (finite domain constraints like a_i \in [expr1, expr2] with
     * expr1 and expr2 as FDBoundaries), storing the result in this.
     *
     * @param constraints SimplePolyConstraints of type GE or EQ
     * @param searchStrictCs of type GE, at least one of them is to be
     *  oriented strictly
     * @param additionalConstraints SimplePolynomials, implicitly
     *  treated as SimplePolyConstraints of type EQ
     */
    private void translate(List<SimplePolyConstraint> constraints,
            List<SimplePolyConstraint> searchStrictCs,
            List<SimplePolynomial> additionalConstraints)
                throws AbortionException {
        for (SimplePolynomial sp : additionalConstraints) {
            this.aborter.checkAbortion();
            this.translate(new SimplePolyConstraint(sp, ConstraintType.EQ), false);
        }

        for (SimplePolyConstraint spc : constraints) {
            this.aborter.checkAbortion();
            this.translate(spc, false);
        }

        for (SimplePolyConstraint spc : searchStrictCs) {
            this.aborter.checkAbortion();
            this.translate(spc, true);
        }

    // DEBUG
    /*
    System.out.println("constraints:");
    int i = 0;
    for (Iterator iter = this.constraints.iterator(); iter.hasNext();) {
      FiniteDomain FD = (FiniteDomain) iter.next();
      System.out.println(""+i+": "+FD);
      i++;
    }
    System.out.println(this.constraints.size() + " constraints over " + occ.size() + " variables.");
    System.out.println("Range: "+this.range);
    System.out.println();
    System.out.println("dpg:");
    for (Iterator iter = this.dpg.entrySet().iterator(); iter.hasNext();) {
      Entry entry = (Entry) iter.next();
      System.out.println(entry.getKey() + " = " + entry.getValue());
    }
    System.out.println();
    System.out.println("occ:");
    for (Iterator iter = this.occ.entrySet().iterator(); iter.hasNext();) {
      Entry entry = (Entry) iter.next();
      System.out.println(entry.getKey() + " = " + entry.getValue());
    } */
    // END
    }

    /**
     * docu-guess (fuhs):
     * @param constraint to be converted into a FiniteDomain,
     *  which is stored in this
     * @param isSearchStrict whether constraint is a searchStrictConstraint
     *  such that this.searchStrictFDs gets the indices of the resulting
     *  FiniteDomains along with which of the boundaries is to be changed
     *  for searchstrict
     */
  private void translate(SimplePolyConstraint constraint, boolean isSearchStrict) {
    if (constraint.getType() == ConstraintType.GE) {
        constraint.getPolynomial().getInequalityConstraints(this, isSearchStrict);
    } else {
        constraint.getPolynomial().getEqualityConstraints(this);
    }
  }

}
