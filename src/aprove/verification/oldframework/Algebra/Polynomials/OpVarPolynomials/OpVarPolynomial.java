package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials;

import static aprove.verification.oldframework.Algebra.Polynomials.ConstraintType.*;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * A VarPolynomial where also max(.,.) and min(.,.) are allowed expressions.
 * As for VarPolynomials, we assume that variables are only instantiated
 * with non-negative integers.
 *
 * The implementation uses VarPolynomials with "hook" variables which serve
 * as placeholders for mapped to max- and min-expressions.
 * (A little bit of a hack, but got our RTA'08 paper done in time.)
 *
 * @author fuhs
 * @version $Id$
 */
public class OpVarPolynomial implements Exportable, XMLObligationExportable {

    private final VarPolynomial hookPoly;

    // maps placeholder variables to a triple:
    //  1)          true: max, false: min
    //  2) and 3):  the args of the operator from 1)
    private final Map<String, OpApp> varsToOpArgs;

    public static final OpVarPolynomial ZERO = new OpVarPolynomial(VarPolynomial.ZERO);

    private OpVarPolynomial(final VarPolynomial hookPoly,
            final Map<String, OpApp> varMap) {
        if (Globals.useAssertions) {
            assert hookPoly != null;
            assert varMap != null;
            assert hookPoly.getVariables().containsAll(varMap.keySet());
        }
        this.hookPoly = hookPoly;
        this.varsToOpArgs = varMap;
    }

    private OpVarPolynomial(final VarPolynomial poly) {
        this(poly, Collections.<String, OpApp>emptyMap());
    }

    /**
     * Creates a new OpVarPolynomial consisting of hookPoly with
     * varMap assigning max/min-expressions to certain variables
     * ("hook variables") in hookPoly. Here, (true, p, q) means
     * max(p, q) and (false, p, q) means min(p, q).
     *
     * @param hookPoly
     * @param varMap
     * @return
     */
    public static OpVarPolynomial create(final VarPolynomial hookPoly,
            final Map<String, OpApp> varMap) {
        return new OpVarPolynomial(hookPoly, varMap);
    }

    /**
     * @param poly - to be encapsulated by this
     * @return poly as OpVarPolynomial
     */
    public static OpVarPolynomial create(final VarPolynomial poly) {
        return new OpVarPolynomial(poly);
    }

    /**
     * @param variable - to be encapsulated by this
     * @return variable as OpVarPolynomial
     */
    public static OpVarPolynomial createVariable(final String variable) {
        final VarPolynomial poly = VarPolynomial.createVariable(variable);
        return new OpVarPolynomial(poly);
    }


    /**
     * Adds addend to this and returns the result.
     * this is not modified in the process.
     * The arguments of max/min-expressions, however,
     * will be shared with the result.
     *
     * Precondition: addend must not contain any of the variables that
     * are used as hooks for max/min-expressions in this.
     *
     * @param addend - to be added to this
     * @return the sum of this and addend
     */
    public OpVarPolynomial plus(final OpVarPolynomial addend) {
        if (Globals.useAssertions) {
            assert Collections.disjoint( addend.varsToOpArgs.keySet(),
                    this.varsToOpArgs.keySet() ) : "hook var clash";
            assert Collections.disjoint( addend.varsToOpArgs.keySet(),
                    this.hookPoly.getVariables() ) : "hook var clash";
            assert Collections.disjoint( this.varsToOpArgs.keySet(),
                    addend.hookPoly.getVariables() ) : "hook var clash";
        }
        final VarPolynomial newHook = this.hookPoly.plus(addend.hookPoly);
        Map<String, OpApp> newVarsToOpArgs;
        newVarsToOpArgs = new LinkedHashMap<String, OpApp>(this.varsToOpArgs.size() + addend.varsToOpArgs.size());
        newVarsToOpArgs.putAll(this.varsToOpArgs);
        newVarsToOpArgs.putAll(addend.varsToOpArgs);
        return OpVarPolynomial.create(newHook, newVarsToOpArgs);
    }


    /**
     * Adds addend to this and returns the result.
     * this is not modified in the process.
     * The arguments of max/min-expressions, however,
     * will be shared with the result.
     *
     * Precondition: addend must not contain any of the variables that
     * are used as hooks for max/min-expressions in this.
     *
     * @param addend - to be added to this
     * @return the sum of this and addend
     */
    public OpVarPolynomial plus(final VarPolynomial addend) {
        if (Globals.useAssertions) {
            assert Collections.disjoint( addend.getVariables(),
                    this.varsToOpArgs.keySet() )
                    : "adding a polynomial to this which contains hook variables is a bad idea!";
        }
        final VarPolynomial newHook = this.hookPoly.plus(addend);
        return OpVarPolynomial.create(newHook, this.varsToOpArgs);
    }

    /**
     * Adds addend to this and returns the result.
     * this is not modified in the process.
     *
     * The arguments of max/min-expressions, however,
     * will be shared with the result.
     *
     * @param addend - to be added to this
     * @return the sum of this and addend
     */
    public OpVarPolynomial times(final SimplePolynomial factor) {
        final VarPolynomial newHook = this.hookPoly.times(factor);
        return OpVarPolynomial.create(newHook, this.varsToOpArgs);
    }

    public OpVarPolynomial substituteVarsWithOpVPs(final Map<String, OpVarPolynomial> substitution, final IndexedNameGenerator gen) {
        // make sure that no bound variables are substituted
        if (Globals.useAssertions) {
            assert Collections.disjoint(this.varsToOpArgs.keySet(),
                    substitution.keySet());
        }

        // substitute both in the hookPoly and in the arg polys (if any)
        OpVarPolynomial result;
        if (this.isAtomic()) {
            // no args to substitute in any more
            result = this.hookPoly.substituteVarsWithOpVPs(substitution);
        }
        else {
            final Map<String, OpApp> newVarsToOpArgs = new LinkedHashMap<String, OpApp>();

            final Map<String, OpVarPolynomial> hookSubst = new LinkedHashMap<String, OpVarPolynomial>(substitution);
            // combines substitution and the insertion of fresh hook variables

            for (final Entry<String, OpApp> varToOpApp : this.varsToOpArgs.entrySet()) {
                OpApp oldOpApp, newOpApp;
                oldOpApp = varToOpApp.getValue();
                final OpVarPolynomial newFirstArg  = oldOpApp.getLeftArg().substituteVarsWithOpVPs(substitution, gen);
                final OpVarPolynomial newSecondArg = oldOpApp.getRightArg().substituteVarsWithOpVPs(substitution, gen);
                newOpApp = oldOpApp.createWithNewArgs(newFirstArg, newSecondArg);

                // use a fresh hook variable for the new max-/min-expression
                final String newHookVar = gen.next();
                newVarsToOpArgs.put(newHookVar, newOpApp);

                // make sure that the hookVar is used in the hookPoly as well
                hookSubst.put(varToOpApp.getKey(), OpVarPolynomial.createVariable(newHookVar));
            }

            final OpVarPolynomial newHook = this.hookPoly.substituteVarsWithOpVPs(hookSubst);
            newVarsToOpArgs.putAll(newHook.varsToOpArgs);
            result = new OpVarPolynomial(newHook.hookPoly, newVarsToOpArgs);
        }
        return result;
    }


    /**
     * Computes a version of this in which the coefficients of this that occur
     * in the key set of values are replaced by the corresponding numerical
     * values indicated by values.
     *
     * @param values coefficient-to-value mapping for known coefficient values
     * @return the specialized OpVarPolynomial
     */
    public OpVarPolynomial specialize(final Map<String, BigInteger> values) {
        final VarPolynomial newHookPoly = this.hookPoly.specialize(values);
        final Set<String> newHookPolyAllVars = newHookPoly.getVariables();

        Map<String, OpApp> newVarsToOpArgs;
        newVarsToOpArgs = new LinkedHashMap<String, OpApp>(this.varsToOpArgs.size());
        for (final Entry<String, OpApp> varToOpArg : this.varsToOpArgs.entrySet()) {
            final String oldHookVar = varToOpArg.getKey();
            // maybe also oldHookVar has disappeared during the
            // specialization of this.hookPoly; then the expression
            // it stood for should be disregarded
            if (newHookPolyAllVars.contains(oldHookVar)) {
                OpApp oldOpApp, newOpApp;
                oldOpApp = varToOpArg.getValue();
                OpVarPolynomial newArg1, newArg2;
                newArg1 = oldOpApp.getLeftArg().specialize(values);
                newArg2 = oldOpApp.getRightArg().specialize(values);

                // TODO check whether newArg1 and newArg2 are in >= or <= for
                // all valuations, then we could get rid of this pesky OpApp

                newOpApp = oldOpApp.createWithNewArgs(newArg1, newArg2);
                newVarsToOpArgs.put(oldHookVar, newOpApp);
            }
        }
        return new OpVarPolynomial(newHookPoly, newVarsToOpArgs);
    }

    public boolean containsVariable(final String x) {
        if (this.hookPoly.containsVariable(x)) {
            return ! this.varsToOpArgs.containsKey(x);
        }
        for (final OpApp opApp : this.varsToOpArgs.values()) {
            if (opApp.getLeftArg().containsVariable(x) || opApp.getRightArg().containsVariable(x)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return true iff this does not contain any max or min
     */
    public boolean isAtomic() {
        return this.varsToOpArgs.isEmpty();
    }

    /**
     * @return true iff there are no abstract coefficients in this
     *  (i.e., all occurring SimplePolynomials are just numbers)
     */
    public boolean isConcrete() {
        if (! this.hookPoly.isConcrete()) {
            return false;
        }
        for (final OpApp opApp : this.varsToOpArgs.values()) {
            if ((! opApp.getLeftArg().isConcrete()) ||
                (! opApp.getRightArg().isConcrete())) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return whether all numerical coeffs that occur in this are positive
     */
    public boolean allPositive() {
        if (! this.hookPoly.allPositive()) {
            return false;
        }
        for (final OpApp opApp : this.varsToOpArgs.values()) {
            if ((! opApp.getLeftArg().allPositive()) ||
                (! opApp.getRightArg().allPositive())) {
                return false;
            }
        }
        return true;
    }

    /**
     * @param substitutor - used to perform VarPolynomial substitution
     * @return list of CondVarPolynomials that correspond to this; here, the
     *  case analysis at each max/min-application is explicitly performed
     */
    public List<CondVarPolynomial> getCondVPs(final VPSubstitutor substitutor) {
        if (this.isAtomic()) {
            // in this case, we get the hookPoly as CondVP and are done with it
            final CondVarPolynomial condVP = new CondVarPolynomial(this.hookPoly);
            return Collections.singletonList(condVP);
        }

        final Map<String, List<CondVarPolynomial>> condVPsOfArgs = this.getCondVPsOfArgs(substitutor);

        // now we need to build all (sensible) possible combinations of substitutions
        // for the variables which represent an OpVarPolynomial:
        // E.g., in          y1  + 3*        y2  - 7*        y3  standing for
        //           max(p1, q1) + 3*max(p2, q2) - 7*max(p3, q3), we collect
        // the conditions for y1, y2, and y3, and then we build conditional
        // values for y1, y2, and y3. Those which are consistent with each other
        // are then combined to corresponding conditional polys for this.

        // * split map into two lists of keys and values
        final int size = condVPsOfArgs.size();
        final List<String> variables = new ArrayList<String>(size);
        final List<List<CondVarPolynomial>> condVPsList = new ArrayList<List<CondVarPolynomial>>(size);

        for (final Entry<String, List<CondVarPolynomial>> e : condVPsOfArgs.entrySet()) {
            // collect variables and condVPs
            variables.add(e.getKey());
            final List<CondVarPolynomial> condVPs = e.getValue();
            condVPsList.add(condVPs);
        }

        // * apply ListGenerator to get lists of values, immediately
        //   generate the corresponding substitution from these lists,
        //   and perform them on this.hookPoly; then we finally obtain
        //   the resulting CondVPs for this.
        final List<CondVarPolynomial> result = new ArrayList<CondVarPolynomial>();
        final ListGenerator<CondVarPolynomial> listGen = new ListGenerator<CondVarPolynomial>(condVPsList, true);

        int debugInconsistentCount = 0; // TODO ditch
        listGenLoop: while (listGen.hasNext()) {
            final List<CondVarPolynomial> substCVPs = listGen.next();
            // check: can any inconsistencies be found in the
            // conditions that we get in all the elements of substCVPs
            // if so, we ignore any constraint that would result from
            // (false /\ _ => _) always holds

            // check each element combined with each other one;
            // here we rely on substCVPs.get(i) being efficient
            boolean inconsistent = false;
            final int listSize = substCVPs.size();
            for (int i = 0; i < listSize; ++i) {
                final CondVarPolynomial condVP1 = substCVPs.get(i);
                for (int j = i + 1; j < listSize; ++j) {
                    final CondVarPolynomial condVP2 = substCVPs.get(j);
                    inconsistent = condVP1.checkCondsForInconsistency(condVP2);
                    if (inconsistent) {
                        ++debugInconsistentCount;
                        continue listGenLoop;
                    }
                }
            }

            final Map<String, VarPolynomial> substitution = new LinkedHashMap<String, VarPolynomial>(size);

            int i = 0; // for the variables
            for (final CondVarPolynomial condVP : substCVPs) {
                final String var = variables.get(i);
                ++i;
                final VarPolynomial substituteForVar = condVP.getPoly();
                substitution.put(var, substituteForVar);
            }

            // apply substitution ...
            final VarPolynomial hookPolyAfterSubstitution = substitutor.substitute(this.hookPoly,
                    substitution);

            // ... and build the resulting CondVarPolynomial.
            final CondVarPolynomial resultElement = new CondVarPolynomial(substCVPs,
                    null, hookPolyAfterSubstitution);
            result.add(resultElement);
        }

        return result;
    }

    /**
     * @param substitutor - used for performing VarPolynomial substitution
     * @return a map from the variables used as placeholders for max/min/...
     *  to the CondVPs that constitute their possible values
     */
    private Map<String, List<CondVarPolynomial>> getCondVPsOfArgs(final VPSubstitutor substitutor) {
        Map<String, List<CondVarPolynomial>> condVPsOfArgs;
        condVPsOfArgs = new LinkedHashMap<String, List<CondVarPolynomial>>(this.varsToOpArgs.size());

        // first get the conditional polynomials of the args
        // (found in varsToOpArgs.values()) ...
        for (final Entry<String, OpApp> e : this.varsToOpArgs.entrySet()) {
            final OpApp opApp = e.getValue();
            final boolean isMax = opApp.isMax();

            List<CondVarPolynomial> condVPsLeftArg, condVPsRightArg, condVPsForVar;
            condVPsLeftArg  = opApp.getLeftArg().getCondVPs(substitutor);
            condVPsRightArg = opApp.getRightArg().getCondVPs(substitutor);
            condVPsForVar = new ArrayList<CondVarPolynomial>(condVPsLeftArg.size() * condVPsRightArg.size() * 2);

            // Now build CondVPs which have one of condVPsLeftArg (cvp1),
            // one of condVPsRightArg (cvp2), and
            // (cvp1.value >= cvp2.value) or !(cvp1.value >= cvp2.value)
            // as conditions
            // and the corresponding greater polynomial from the last condition
            // as value.

            // * conditions and value:
            for (final CondVarPolynomial cvp1 : condVPsLeftArg) {
                for (final CondVarPolynomial cvp2 : condVPsRightArg) {
                    final List<CondVarPolynomial> cvpsOfCurrentArg = new ArrayList<CondVarPolynomial>(2);

                    // check: can any inconsistencies be found in the
                    // conditions that we get here?
                    // if so, we ignore any constraint that would result since
                    // (false /\ _ => _) always holds
                    if (! cvp1.checkCondsForInconsistency(cvp2)) {
                        cvpsOfCurrentArg.add(cvp1);
                        cvpsOfCurrentArg.add(cvp2);

                        // now for the last condition. here we need to compare
                        // the values of cvp1 and cvp2.
                        VarPolynomial cvp1Value, cvp2Value;
                        cvp1Value = cvp1.getPoly();
                        cvp2Value = cvp2.getPoly();

                        VarPolyConstraint cond1GE2;
                        cond1GE2 = new VarPolyConstraint(cvp1Value.minus(cvp2Value), GE);
                        if ((! cond1GE2.isUnsatisfiable()) &&
                            (! cvp1.checkCondForInconsistency(cond1GE2)) &&
                            (! cvp2.checkCondForInconsistency(cond1GE2))) {
                            CondVarPolynomial cvp1GE2;
                            if (isMax) {
                                cvp1GE2 = new CondVarPolynomial(cvpsOfCurrentArg, cond1GE2, cvp1Value);
                            }
                            else {
                                cvp1GE2 = new CondVarPolynomial(cvpsOfCurrentArg, cond1GE2, cvp2Value);
                            }
                            condVPsForVar.add(cvp1GE2);
                        }

                        VarPolyConstraint notCond1GE2;
                        notCond1GE2 = new VarPolyConstraint(cvp2Value.minus(VarPolynomial.ONE).minus(cvp1Value), GE);
                        if ((! notCond1GE2.isUnsatisfiable()) &&
                            (! cvp1.checkCondForInconsistency(notCond1GE2)) &&
                            (! cvp2.checkCondForInconsistency(notCond1GE2))) {
                            CondVarPolynomial cvp2GE1;
                            if (isMax) {
                                cvp2GE1 = new CondVarPolynomial(cvpsOfCurrentArg, notCond1GE2, cvp2Value);
                            }
                            else {
                                cvp2GE1 = new CondVarPolynomial(cvpsOfCurrentArg, notCond1GE2, cvp1Value);
                            }
                            condVPsForVar.add(cvp2GE1);
                        }

                    }
                }
            }

            // Then map the corresponding variables in hookPoly to these
            // possible values and store the result in condVPsOfArgs.
            condVPsOfArgs.put(e.getKey(), condVPsForVar);
        }
        return condVPsOfArgs;
    }

    /**
     * @return the hookPoly
     */
    public VarPolynomial getHookPoly() {
        return this.hookPoly;
    }


    /**
     * @return the varsToOpArgs - modify only if you know what you are doing!
     */
    public Map<String, OpApp> getVarsToOpArgs() {
        return this.varsToOpArgs;
    }

    @Override
    public String toString() {
        if (true) {
            // very much of a hack, but /should/ work
            final Map<String, VarPolynomial> subst = new LinkedHashMap<String, VarPolynomial>();
            for (final Entry<String, OpApp> e : this.varsToOpArgs.entrySet()) {
                final StringBuilder b = new StringBuilder();
                final OpApp opApp = e.getValue();
                if (opApp.isMax()) {
                    b.append("max(");
                }
                else {
                    b.append("min(");
                }
                b.append(opApp.getLeftArg());
                b.append(", ");
                b.append(opApp.getRightArg());
                b.append(")");

                // uaaah ... ah well.
                final VarPolynomial poly = VarPolynomial.createVariable(b.toString());
                subst.put(e.getKey(), poly);
            }
            final VarPolynomial resultPoly = this.hookPoly.substituteVariables(subst);
            final String result = resultPoly.toString();
            return result;
        }
        else {
            // less hackish, but also less readable
            final StringBuilder b = new StringBuilder("[");
            b.append(this.hookPoly.toString());
            if (! this.isAtomic()) {
                b.append(", where: ");
                boolean first = true;
                for (final Entry<String, OpApp> e : this.varsToOpArgs.entrySet()) {
                    if (first) {
                        first = false;
                    }
                    else {
                        b.append(" ; ");
                    }
                    b.append(e.getKey());
                    b.append(" = ");
                    final OpApp opApp = e.getValue();
                    if (opApp.isMax()) {
                        b.append("max(");
                    }
                    else {
                        b.append("min(");
                    }
                    b.append(opApp.getLeftArg());
                    b.append(", ");
                    b.append(opApp.getRightArg());
                    b.append(")");

                }
            }
            b.append("]");
            return b.toString();
        }
    }

    @Override
    public String export(final Export_Util o) {
        return this.export(o, new HashMap<String, String>());
    }

    /**
     * Like export(Export_Util), but varRepresentations indicates how the
     * hook variables are supposed to be displayed.
     *
     * @param eu
     * @param varRepresentations
     * @return
     */
    private String export(final Export_Util o, final Map<String, String> hookVarRepresentations) {
        // - export args
        for (final Entry<String, OpApp> varToOpApp : this.varsToOpArgs.entrySet()) {
            final String hookVar = varToOpApp.getKey();

            // maybe we have already seen hookVar, no need to compute it twice
            // (relying on the assumption that in any OpVarPolynomial, a hookVar
            // is supposed to denote the same max-/min-expression wherever it
            // occurs)
            String exportedOpApp = hookVarRepresentations.get(hookVar);
            if (exportedOpApp == null) {
                final OpApp opApp = varToOpApp.getValue();
                final String exportedArg1 = opApp.getLeftArg().export(o, hookVarRepresentations);
                final String exportedArg2 = opApp.getRightArg().export(o, hookVarRepresentations);
                final StringBuilder builder = new StringBuilder();
                builder.append(opApp.isMax() ? "max(" : "min(");
                builder.append(exportedArg1);
                builder.append(", ");
                builder.append(exportedArg2);
                builder.append(")");
                exportedOpApp = builder.toString();
                hookVarRepresentations.put(hookVar, exportedOpApp);
            }
        }

        // - export hookPoly, using exported args to represent the hookVars
        return this.hookPoly.export(o, hookVarRepresentations);
    }

    @Override
    public int hashCode() {
        return this.hookPoly.hashCode() + 7*this.varsToOpArgs.hashCode();
    }

    @Override
    public boolean equals(final Object o) {
        if (!(o instanceof OpVarPolynomial)) {
            return false;
        }
        final OpVarPolynomial that = (OpVarPolynomial) o;
        return this.hookPoly.equals(that.hookPoly) && this.varsToOpArgs.equals(that.varsToOpArgs);
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {

        final Map<String, Element> subTrees = new LinkedHashMap<String, Element>();
        for (final Map.Entry<String, OpApp> opApp : this.varsToOpArgs.entrySet()) {
            subTrees.put(opApp.getKey(), opApp.getValue().toDOM(doc, xmlMetaData));
        }
        return this.hookPoly.toDOM2(doc, subTrees, xmlMetaData);
    }

}
