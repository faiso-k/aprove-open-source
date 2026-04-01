package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;


import java.math.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 *
 * docu-guess (fuhs):
 * Provides a search method which searches for solutions for an instance of
 * FDConstraints.
 */
public class FDSearch extends AbstractSearchAlgorithm {

  // DEBUG
 // int counter = 0;
  // END


  private static Logger log =
    Logger.getLogger("aprove.verification.oldframework.Algebra.Orders.Utility.POLO.FDSearch");

  private Abortion aborter;


  private FDSearch(DefaultValueMap<String, BigInteger> ranges) {
    super(ranges);
  }

  public static FDSearch create(DefaultValueMap<String, BigInteger> ranges) {
    return new FDSearch(ranges);
  }


    /**
     * docu-guess (fuhs):
     * Chooses the best variable among those on which some FiniteDomain
     * in FDConstraints depends according to the following criteria:
     * (1) Its value must not have been fixed (according to state).
     * (2) Its possible minimal value according to state is minimal
     *     compared to those of the other candidates.
     * (3) Its possible minimal value according to state is minimal
     *     compared to those of the other candidates and:
     *       Its possible maximal value is minimal compared those of the
     *       other candidates with minimal possible minimal (sic!) value
     *       or it occurs more often in fdc than the other candidates
     *       (here, greater variables with respect to the lexicographic
     *       ordering will win in case of doubt).
     *
     * @param fdc contains the FiniteDomains to solve and information
     *  regarding how many variables occur in the intervals of the
     *  FiniteDomains
     * @param state maps String -> IntegerInterval, var |-> [m,n]
     * @return the "best" variable, or null in case there is no variable
     *  whose value has not been fixed by state
     */
  private String chooseBestVariable(FDConstraints fdc, Map<String, BigIntegerInterval> state) {
    String best_var = null;
    BigInteger best_min = fdc.range.add(BigInteger.ONE);
    BigInteger best_diff = best_min;
    int best_occ = 0;

    for (Entry<String, Integer> entry : fdc.occ.entrySet()) {
      String var = entry.getKey();
      BigIntegerInterval interval = state.get(var);

      int intervalMinCompareToBestMin = interval.min.compareTo(best_min);

      if (intervalMinCompareToBestMin > 0) {
        continue;
    }

      if (interval.min.equals(interval.max)) {
        continue;
    }

      BigInteger diff = interval.max.subtract(interval.min);
      int occ = entry.getValue();

      if ((intervalMinCompareToBestMin < 0) || (diff.compareTo(best_diff) < 0) || (occ > best_occ)) {
        best_var = var;
        best_min = interval.min;
        best_diff = diff;
        best_occ = occ;
      }

    }

    return best_var;
  }

    /**
     * docu-guess (fuhs):
     * Tries to deduce further restrictions on the IntegerIntervals in which
     * the variable values of the FiniteDomains in activeCs lie according
     * to state (compare paper, Fig. 2).
     *
     * @param activeCs number of the currently "active" FiniteDomains
     * @param fdc contains the FiniteDomains for which a solution is wanted
     * @param state mapping [String -> IntegerInterval], maps variables
     *  to their minimal and maximal possible values
     * @return false if activeCs turn out to be unsolvable, true otherwise
     */
  private boolean evaluate(Set<Integer> activeCs, FDConstraints fdc,
                           Map<String, BigIntegerInterval> state) {
      if (activeCs == null) {
          return true;
      }
      activeCs = new LinkedHashSet<Integer>(activeCs);
      for (Iterator<Integer> iter = activeCs.iterator(); iter.hasNext();) {
          Integer element = iter.next();
          iter.remove();

          FiniteDomain fd = fdc.constraints.get(element);
          BigIntegerInterval interval = state.get(fd.variable);

          BigInteger newMin;
          try {
              newMin = fd.getMin(state);
          } catch (ArithmeticException e) {
              newMin = interval.min;
          } catch (NotSolveableException e) {
              return false;
          }

          BigInteger newMax;
          try {
              newMax = fd.getMax(state);
          } catch (ArithmeticException e) {
              newMax = interval.max;
          } catch (NotSolveableException e) {
              return false;
          }

          if ((newMin.compareTo(interval.min) > 0) || (newMax.compareTo(interval.max)) < 0) {
              BigInteger min = newMin.max(interval.min);
              BigInteger max = newMax.min(interval.max);

              if (min.compareTo(max) > 0) {
                  return false;
              }

              BigIntegerInterval newIntervall = new BigIntegerInterval(min, max);
              state.put(fd.variable, newIntervall);
              Set<Integer> dependentConstraints = fdc.dpg.get(fd.variable);
              if (dependentConstraints != null) {
                activeCs.addAll(dependentConstraints);
            }

              iter = activeCs.iterator();
          }
      }

      return true;
  }

    /**
     * docu-guess (fuhs):
     * Searches for a solution for constraints and returns it as a mapping
     * of the coefficients to values by which all constraints should be
     * satisfied.
     *
     * @param constraints the SimplePolyConstraints for which a solution is desired
     * @param searchStrictConstraints is non-empty in SEARCHSTRICT mode:
     *  try to find a solution by which we can order at least one of these
     *  constraints strictly; all elements of searchStrictConstraints must be
     *  of type GE
     * @param maximizeMe ignored
     * @param aborter the aborter
     * @return the resulting State, i.e. a mapping [String -> Integer] which
     *  maps (indefinite) coefficients to their numerical values.
     */
  @Override
public Map<String, BigInteger> search(Set<SimplePolyConstraint> constraints,
                                     Set<SimplePolyConstraint> searchStrictConstraints,
                                     SimplePolynomial maximizeMe, Abortion aborter) throws AbortionException {

      this.aborter = aborter;

      // make sure that the variable-dependent ranges are respected
      constraints = new LinkedHashSet<SimplePolyConstraint>(constraints);
      BigInteger maxRange = super.addRangeConstraints(constraints, searchStrictConstraints);

      // DEBUG
    /*
    System.out.println("Constraints to solve:");
    for (Iterator iter = constraints.iterator(); iter.hasNext();) {
      PolyConstraint c = (PolyConstraint) iter.next();
      System.out.println(c);
    }
    System.out.println();
     */
    // END

    FDSearch.log.log(Level.CONFIG, "Translating polynomials to finite domains...\n");

    // translate polynomial constraints to fd constraints
    FDConstraints fdc;
    try {
        fdc = FDConstraints.create(this.aborter, constraints,
                                   searchStrictConstraints,
                                   maxRange);
    } catch (UnsolveableConstraintException e) {
        return null;
    }


    FDSearch.log.log(Level.CONFIG, "Starting search...\n");

    this.aborter.checkAbortion();

    if (searchStrictConstraints.isEmpty()) {
        return this.searchOnFDConstraints(fdc);
    }
    else {
        // try to order one of searchStrictConstraints strictly
        Map<Integer, Boolean> oldIndexMap = null;
        for (Map<Integer, Boolean> newIndexMap : fdc.searchStrictFDs) {
            if (oldIndexMap != null) {
                // undo the orientation of one constraint from the previous
                // attempt
                for (Entry<Integer, Boolean> oldEntry : oldIndexMap.entrySet()) {
                    int i = oldEntry.getKey();
                    FiniteDomain fd = fdc.constraints.get(i).toNonStrict(oldEntry.getValue());
                    fdc.constraints.set(i, fd);
                }
            }
            for (Entry<Integer, Boolean> newEntry : newIndexMap.entrySet()) {
                int i = newEntry.getKey();
                FiniteDomain fd = fdc.constraints.get(i).toStrict(newEntry.getValue());
                fdc.constraints.set(i, fd);
            }
            Map<String, BigInteger> solution = this.searchOnFDConstraints(fdc);
            if (solution != null) {
                return solution;
            }
            oldIndexMap = newIndexMap;
        }
        // none of searchStrictConstraints could be ordered strictly
        return null;
    }

  }

  /**
   * The actual solving method.
   *
   * @param fdc the FDConstraints which is to be solved
   * @return map indefinite -> numerical value (values for the coefficients)
   *  if a solution was found, else null
   */
  private Map<String, BigInteger> searchOnFDConstraints(FDConstraints fdc)
      throws AbortionException {
      Set<Integer> activeCs = new LinkedHashSet<Integer>(fdc.constraints.size());
      for (int i = 0; i < fdc.constraints.size(); ++i) {
        activeCs.add(i);
    }

      // create initial state
      Map<String, BigIntegerInterval> state = new LinkedHashMap<String, BigIntegerInterval>(fdc.ranges.size());
      // use LinkedHashMap for fast iterators

      for (Entry<String, BigInteger> entry : fdc.ranges.entrySet()) {
        String variable = entry.getKey();
        state.put(variable, new BigIntegerInterval(BigInteger.ZERO, entry.getValue()));
      }


      state = this.solve(activeCs, fdc, state);


      if (state == null) {
        return null;
    }


      Map<String, BigInteger> solution = new LinkedHashMap<String, BigInteger>(fdc.ranges.size());
      for (String variable : fdc.ranges.keySet()) {
        solution.put(variable, state.get(variable).min);
      }

      return solution;
  }

    /**
     * docu-guess (fuhs):
     * Computes a solution state for the FiniteDomains corresponding to
     * activeCs in fdc.
     * @return the solution found
     */
  private Map<String, BigIntegerInterval> solve(Set<Integer> activeCs, FDConstraints fdc,
                                             Map<String, BigIntegerInterval> state) throws AbortionException {
      // doku-guess (thiemann):
      // activeCs :: [Int] : the set of numbers whose constraints that are active
      // state :: coeff -> [min,max] : a mapping for each coefficient into its Interval
      // fdc :: the finite domain constraints

      // DEBUG
      // ++this.counter;
      //      System.out.println(state);
      // END

      this.aborter.checkAbortion();

      // forward closure, propagation
      if (!this.evaluate(activeCs, fdc, state)) {
          return null;
      }

      String variable = this.chooseBestVariable(fdc, state);

      if (variable == null) {
          // solution found
          return state;
      }

      BigIntegerInterval interval = state.get(variable);

      // DEBUG
      //System.out.println("Weiter mit: " + variable + " (Min.)"+interval);
      // END
      Map<String, BigIntegerInterval> s = new LinkedHashMap<String, BigIntegerInterval>(state);
      s.put(variable, new BigIntegerInterval(interval.min, interval.min));

      Set<Integer> dependentConstraints = fdc.dpg.get(variable);
      s = this.solve(dependentConstraints, fdc, s);

      if (s != null) {
        return s;
    }

      // DEBUG
      //System.out.println("Weiter mit: " + variable + " (Rest)"+interval);
      // END
      s = new LinkedHashMap<String, BigIntegerInterval>(state);
      s.put(variable, new BigIntegerInterval(interval.min.add(BigInteger.ONE), interval.max));

      return this.solve(dependentConstraints, fdc, s);
  }

  @Override
public boolean introducesFreshVariables() {
      // FDSearch introduces fresh variables due to product abstraction
      return true;
  }
}
