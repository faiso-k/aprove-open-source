package aprove.verification.dpframework.Orders.Utility.PMATRO;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.PolyMatrices.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Note on extended monotonicity:
 * The strict greater relation must be monotone in addition to
 * the weak one. This is made sure by enforcing that the first entries of each
 * non-constant coefficient matrix are nonzero.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class NatPolyMatrixInterpretation extends AbstractPolyMatrixInterpretation<BigIntImmutable> {

    protected ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu;

    protected NatPolyMatrixInterpretation(
            final Semiring<BigIntImmutable> ringC,
            final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fv,
            final OrderPolyFactory<BigIntImmutable> coeffPolyFactory,
            final PolyMatrixFactory<BigIntImmutable> matrixFactory,
            final ConstraintFactory<BigIntImmutable> constraintFactory,
            final int dimension,
            final boolean allstrict,
            final Set<FunctionSymbol> collapsingSyms,
            final String description,
            final List<Citation> citations,
            final ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu) {
        super(ringC, coeffPolyFactory, matrixFactory, constraintFactory,
            fv, dimension, allstrict, collapsingSyms, description, citations);
        this.matroType   = "int";
        this.mu          = mu;
    }

    /**
     * Create a new, generic matrix interpretation for the
     * function symbols that occur in the specified constraints.
     * @param signature signature of the function symbols that
     *  should be interpreted.
     * @param ringC The (semi-)ring of the matrix entries.
     * @param fv A FlatteningVisitor for outer polynomials over C.
     * @param coeffPolyFactory A factory for polynomials.
     * @param matrixFactory A factory for matrices.
     * @param constraintFactory A factory for constraints.
     * @param dimension The matrices' dimension.
     * @param allstrict Whether to orient all pairs strictly or not.
     * @param description Some text describing the interpretation further.
     * @param citations References to papers describing the
     * interpretation further.
     */
    public static NatPolyMatrixInterpretation create(
            final Iterable<FunctionSymbol> signature,
            final Semiring<BigIntImmutable> ringC,
            final FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fv,
            final OrderPolyFactory<BigIntImmutable> coeffPolyFactory,
            final PolyMatrixFactory<BigIntImmutable> matrixFactory,
            final ConstraintFactory<BigIntImmutable> constraintFactory,
            final int dimension,
            final boolean allstrict,
            final Set<FunctionSymbol> collapsingSyms,
            final String description,
            final List<Citation> citations,
            final ImmutableMap<FunctionSymbol, ? extends Set<Integer>> mu) {
        NatPolyMatrixInterpretation interpretation =
            new NatPolyMatrixInterpretation(ringC, fv, coeffPolyFactory,
                    matrixFactory, constraintFactory, dimension, allstrict,
                    collapsingSyms, description, citations, mu);
        for (FunctionSymbol f : signature) {
            interpretation.extend(f);
        }
        return interpretation;
    }

    /**
     * Performs the actual generation of a generic polynomial matrix
     * interpretation for the function symbol.
     *
     * @param symbol we want its generic interpretation
     * @return a triple consisting of the resulting polynomial matrix interpretation
     * in both collapsed (for working) and "pure" (for displaying) form, and
     * the pre-generated usable rules constraints.
     */
    @Override
    public Triple<PolyMatrix<BigIntImmutable>, Map<GPolyVar, PolyMatrix<BigIntImmutable>>,
                Map<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<BigIntImmutable>>>
            getMatrixFromFunction(final FunctionSymbol symbol, boolean collapse) {
        int arity = symbol.getArity();

        Set<Integer> intSet = null;
        if (this.mu != null)  {
            intSet = this.mu.get(symbol);
        }
        // Prevent null pointer exceptions
        if (intSet == null) {
            intSet = new LinkedHashSet<Integer>();
            for (int i = 0; i < arity; i++) {
                intSet.add(i);
            }
        }

        String constantAddendName = this.getNextCoeffName();
        PolyMatrix<BigIntImmutable> constantAddend =
            this.matrixFactory.buildCoeffVector(constantAddendName, collapse);

        // generate variable names
        List<String> variables = new ArrayList<String>(arity);
        for (int i = 0; i < arity; ++i) {
            variables.add(AbstractPolyMatrixInterpretation.VARIABLE_PREFIX + (i + 1));
        }

        PolyMatrix<BigIntImmutable> sum = constantAddend;
        Map<GPolyVar, PolyMatrix<BigIntImmutable>> actualPol =
            new LinkedHashMap<GPolyVar, PolyMatrix<BigIntImmutable>>();
        actualPol.put(null, constantAddend);

        Map<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<BigIntImmutable>> usableRuleConstraints =
            new LinkedHashMap<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<BigIntImmutable>>();

        for (int i = 0; i < arity; i++) {
            final String coeffName = this.getNextCoeffName();
            final PolyMatrix<BigIntImmutable> coeffMatrix =
                this.matrixFactory.buildCoeffMatrix(coeffName, collapse);
            final PolyMatrix<BigIntImmutable> varCoeffVector =
                this.matrixFactory.buildVarCoeffVector(coeffName,
                    variables.get(i), collapse);

            sum = this.matrixFactory.plus(sum, varCoeffVector);

            actualPol.put(GAtomicVar.createVariable(variables.get(i)),
                    coeffMatrix);

            OrderPoly<BigIntImmutable> firstEntry =
                this.entryPolyFactory.buildFromInnerVariable(
                        GAtomicVar.createVariable(coeffName + "#1"));

            if (this.mu == null || intSet.contains(i)) {
                this.extendedMonotonicityConstraint.add(
                        this.constraintFactory.createWithQuantifier(
                                firstEntry, ConstraintType.GT));
            }

            // pre-generate usable rules constraints
            Set<OrderPolyConstraint<BigIntImmutable>> aConditions =
                this.generateActiveConditions(coeffMatrix);
            Pair<FunctionSymbol, Integer> protoQAC =
                new Pair<FunctionSymbol, Integer>(symbol, i);
            usableRuleConstraints.put(protoQAC, this.constraintFactory.createOr(aConditions));
        }

        return new Triple<PolyMatrix<BigIntImmutable>, Map<GPolyVar, PolyMatrix<BigIntImmutable>>,
                    Map<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<BigIntImmutable>>>(
                sum, actualPol, usableRuleConstraints);
    }

    /**
     * Returns the polynomial constraints resulting from interpreting
     * the terms as matrices and then comparing the entries pairwise.
     */
    @Override
    public OrderPolyConstraint<BigIntImmutable> fromTermConstraints(
            final Collection<Constraint<TRSTerm>> constraints,
            Abortion aborter) throws AbortionException {

        // Step 1: Generate matrix interpretations for the terms and
        // break down the matrix constraints to polynomial ones by
        // pairwise comparison of entries.

        // All of these have to be met.
        Set<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>> weakConditions =
            new LinkedHashSet<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>>();

        // Special range constraints - have to be met, too
        Set<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>> rangeConditions =
            new LinkedHashSet<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>>();

        // One of every set has to be met, unless the set is empty.
        Set<Set<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>>> strongConditions =
            new LinkedHashSet<Set<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>>>();
        for (Constraint<TRSTerm> constraint : constraints) {
            aborter.checkAbortion();
            TermPair tp = TermPair.create(constraint.x, constraint.y);
            PolyMatrix<BigIntImmutable> left =
                this.interpretTerm(tp.getLhsInStandardRepresentation(), aborter);
            PolyMatrix<BigIntImmutable> right =
                this.interpretTerm(tp.getRhsInStandardRepresentation(), aborter);
            OrderRelation rel = constraint.z;
            Set<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>> strongCond = null;

            final int numberOfComponents = left.numRows();
            for (int i = 0; i < numberOfComponents; i++) {
                aborter.checkAbortion();
                strongCond = new LinkedHashSet<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>>();
                if (rel == OrderRelation.EQ) {
                    weakConditions.add(new Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>(
                                left.at(i, 0), right.at(i, 0), ConstraintType.EQ));
                } else { // GT or GE
                    // a > b iff A[i](a_i >= b_i) AND A[0](a_0 > b_0).
                    weakConditions.add(new Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>(
                            left.at(i, 0), right.at(i, 0), ConstraintType.GE)); /*
                    if (rel == Relation.GR) {
                        strongCond.add(new Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>(
                            left.at(i, 0), right.at(i, 0), ConstraintType.GT));
                    }*/
                }
            }
            if (rel == OrderRelation.GR) {
                strongCond.add(new Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>(
                    left.at(0, 0), right.at(0, 0), ConstraintType.GT));
            }
            if (!strongCond.isEmpty()) {
                strongConditions.add(strongCond);
            }
        }

        // Step 2: Apply the absolute positiveness criterion to the
        // constraints, eg. reducing ax+b > cx+d to a>c && b>d

        Set<OrderPolyConstraint<BigIntImmutable>> result =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        for (Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType> triple : weakConditions) {
            result.addAll(this.transformConstraint(triple));
        }
        if (!strongConditions.isEmpty()) {
            Set<OrderPolyConstraint<BigIntImmutable>> strongConstraints =
                new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
            for (Set<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>> strongSet : strongConditions) {
                aborter.checkAbortion();
                for (Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType> triple : strongSet) {
                    strongConstraints.add(this.constraintFactory.createAnd(
                            this.transformConstraint(triple)));
                }
            }
            if (this.allstrict) {
                result.add(this.constraintFactory.createAnd(strongConstraints));
            } else {
                result.add(this.constraintFactory.createOr(strongConstraints));
            }
        }
        OrderPolyConstraint<BigIntImmutable> resultConstraint = this.constraintFactory.createAnd(result);
        resultConstraint = this.constraintFactory.createQuantifierE(
                resultConstraint, resultConstraint.getFreeVariables());
        return resultConstraint;
    }

    /**
     * Kind of similar to fromTermConstraints, but has no allstrict magic
     * involved and only handles a single term constraint. Very handy,
     * e.g., if you do SCNP.
     *
     * @param constraint - use Relation.GR/EQ/GE only
     * @return existential Diophantine OPC whose satisfaction implies
     *  satisfaction of <code>constraint</code>
     */
    public OrderPolyConstraint<BigIntImmutable> termConstraintToExistentialOPC(Constraint<TRSTerm> constraint,
                Abortion aborter)
            throws AbortionException{
        // interpret and get constraints for each component of the vector
        Set<Triple<OrderPoly<BigIntImmutable>,
                   OrderPoly<BigIntImmutable>,
                   ConstraintType>> conditionsWithVars =
            this.termConstraintToOPCsWithVars(constraint, aborter);
        aborter.checkAbortion();

        // now convert conditions, which may still contain universally
        // quantified variables, to a purely existential constraint
        Set<OrderPolyConstraint<BigIntImmutable>> opcs =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
        for (Triple<OrderPoly<BigIntImmutable>,
                    OrderPoly<BigIntImmutable>,
                    ConstraintType> triple : conditionsWithVars) {
            Set<OrderPolyConstraint<BigIntImmutable>> newOpcs =
                this.transformConstraint(triple);
            opcs.addAll(newOpcs);
            aborter.checkAbortion();
        }
        // make them a proper formula (in OPC representation)
        OrderPolyConstraint<BigIntImmutable> resultConstraint =
            this.constraintFactory.createAnd(opcs);
        Set<GPolyVar> eVars = resultConstraint.getFreeVariables();
        resultConstraint = this.constraintFactory.createQuantifierE(resultConstraint, eVars);
        return resultConstraint;
    }

    /**
     * @param constraint - use Relation.GR/EQ/GE only
     * @return a set of triples (l, r, rel) where l and r are polynomials that
     *  may contain (universally quantified) variables such that satisfying
     *  all of these "l rel r" also satisfies <code>constraint</code>
     */
    private Set<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>>
                termConstraintToOPCsWithVars(Constraint<TRSTerm> constraint,
                Abortion aborter) throws AbortionException {
        TermPair tp = TermPair.create(constraint.x, constraint.y);
        PolyMatrix<BigIntImmutable> left =
            this.interpretTerm(tp.getLhsInStandardRepresentation(), aborter);
        aborter.checkAbortion();
        PolyMatrix<BigIntImmutable> right =
            this.interpretTerm(tp.getRhsInStandardRepresentation(), aborter);
        aborter.checkAbortion();
        OrderRelation rel = constraint.z;
        if (Globals.useAssertions) {
            assert rel == OrderRelation.GE || rel == OrderRelation.GR || rel == OrderRelation.EQ;
        }

        // All of these have to be met. ("Set of VarPolyConstraints")
        Set<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>> result =
            new LinkedHashSet<Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>>();

        int numberOfComponents = left.numRows();
        for (int i = 0; i < numberOfComponents; i++) {
            OrderPoly<BigIntImmutable> l = left.at(i, 0);
            OrderPoly<BigIntImmutable> r = right.at(i, 0);
            ConstraintType type = ConstraintType.fromRelation(rel, i == 0);
            result.add(new Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType>(l, r, type));
        }
        return result;
    }

    /**
     * Creates constraints from polynomials by breaking them down
     * into monomials and applying absolute positiveness.
     * @param constraint: a triple with<br>
     * x - the left hand side<br>
     * y - the right hand side<br>
     * z - the constraint/relation type
     * @return a set of constraints representing "x (z) y"
     */
    protected Set<OrderPolyConstraint<BigIntImmutable>> transformConstraint(
            final Triple<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>, ConstraintType> constraint) {

        OrderPoly<BigIntImmutable> leftPoly = constraint.x;
        OrderPoly<BigIntImmutable> rightPoly = constraint.y;
        ConstraintType ct = constraint.z;

        VarPartNode<GPolyVar> varOne =
            this.entryPolyFactory.getInnerFactory().getVarOne();
        OrderPoly<BigIntImmutable> zeroPoly =
            this.entryPolyFactory.buildFromInnerCoeff(BigIntImmutable.ZERO);

        Set<OrderPolyConstraint<BigIntImmutable>> result =
            new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();

        // Flatten the *outer* polynomials (not the inner ones)
        leftPoly.visit(this.fvOuter);
        rightPoly.visit(this.fvOuter);
        Map<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> leftMonomials =
            leftPoly.getMonomials(this.fvOuter.getRingC(), this.fvOuter.getMonoid());
        Map<GMonomial<GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> rightMonomials =
            rightPoly.getMonomials(this.fvOuter.getRingC(), this.fvOuter.getMonoid());
        for (GMonomial<GPolyVar> varPart : leftMonomials.keySet()) {
            // only the constant part needs to be strictly greater for the poly to be
            if (ct == ConstraintType.GT && !varPart.getExponents().isEmpty()) {
                ct = ConstraintType.GE;
            }
            GPoly<BigIntImmutable, GPolyVar> leftCoeff = leftMonomials.get(varPart);
            GPoly<BigIntImmutable, GPolyVar> rightCoeff = rightMonomials.get(varPart);
            OrderPoly<BigIntImmutable> newLeftPoly = this.entryPolyFactory.concat(leftCoeff, varOne);
            // If rightCoeff is a MinusNode, it must be -{[1], [1]}, i.e. 0.
            // Note that the constant part is represented in all polys, even if
            // it is zero.
            if (rightCoeff == null || rightCoeff instanceof MinusNode) {
                result.add(this.constraintFactory.createWithQuantifier(newLeftPoly, ct));
            } else {
                OrderPoly<BigIntImmutable> newRightPoly = this.entryPolyFactory.concat(rightCoeff, varOne);
                result.add(this.constraintFactory.createWithQuantifier(newLeftPoly, newRightPoly, ct));
            }
        }
        // Now check for monomials on the right side which have no corresponding
        // VarPart on the left.
        for (GMonomial<GPolyVar> varPart : rightMonomials.keySet()) {
            if (!leftMonomials.containsKey(varPart)) {
                OrderPoly<BigIntImmutable> newRightPoly = this.entryPolyFactory.concat(
                        rightMonomials.get(varPart), varOne);
                result.add(this.constraintFactory.createWithQuantifier(zeroPoly, newRightPoly, ct));
            }
        }
        return result;
    }

    /**
     * Apply the given variable substitution to the interpretation.
     *
     * @param state maps indefinite coefficient variables to coefficients by
     * which they are supposed to be substituted.
     * @param defValue the value for all those coefficient variables which do
     * not occur.
     * @return an interpretation specialized according to the given map and
     * default value.
     */
    public NatPolyMatrixInterpretation specialize(
            final Map<GPolyVar, BigIntImmutable> state,
            final BigIntImmutable defValue,
            Abortion aborter) throws AbortionException {

        NatPolyMatrixInterpretation specialization =
            new NatPolyMatrixInterpretation(this.ringC, this.fvOuter,
                    this.entryPolyFactory, this.matrixFactory,
                    this.constraintFactory, this.dimension, this.allstrict,
                    this.collapsingSyms, this.description, this.citations,
                    this.mu);

        // make sure not to lose any data here!!!
        specialization.usableRuleConstraints = this.usableRuleConstraints;

        Map<GPolyVar, BigIntImmutable> newState = new LinkedHashMap<GPolyVar, BigIntImmutable>(state);

        for (Entry<FunctionSymbol, PolyMatrix<BigIntImmutable>> entry : this.pol.entrySet()) {
            aborter.checkAbortion();
            PolyMatrix<BigIntImmutable> matrix = entry.getValue();
            List<List<OrderPoly<BigIntImmutable>>> newEntries =
                new ArrayList<List<OrderPoly<BigIntImmutable>>>(matrix.numRows());
            for (int i = 0; i < matrix.numRows(); i++) {
                aborter.checkAbortion();
                List<OrderPoly<BigIntImmutable>> newRow =
                    new ArrayList<OrderPoly<BigIntImmutable>>(matrix.numCols());
                for (int j = 0; j < matrix.numCols(); j++) {
                    OrderPoly<BigIntImmutable> poly = matrix.at(i, j);

                    // replace every variable not in state by defValue
                    for (GPolyVar var : poly.getInnerVariables()) {
                        if (!newState.containsKey(var)) {
                            newState.put(var, defValue);
                        }
                    }
                    poly = this.deepSubstitute(poly, newState, aborter);
                    newRow.add(poly);
                }
                newEntries.add(newRow);
            }
            specialization.pol.put(entry.getKey(),
                    new PolyMatrix<BigIntImmutable>(newEntries));
        }
        specialization.model = newState;

        // also specialize the "visual" representation in actualPol
        for (Entry<FunctionSymbol, Map<GPolyVar, PolyMatrix<BigIntImmutable>>> entry : this.actualPol.entrySet()) {
            aborter.checkAbortion();
            specialization.actualPol.put(entry.getKey(),
                    this.specializeActualPol(entry.getValue(), state, defValue));
        }
        return specialization;
    }

    /**
     * Apply the given substitution to a polynomial in map-representation.
     * @param oldMap The polynomial, represented as a map from
     * variables to coefficients (matrices).
     * @param substitution A variable substitution.
     * @param defaultValue The value to use for variables that are
     * not covered by the substitution.
     * @return The substituted polynomial (map).
     */
    protected Map<GPolyVar, PolyMatrix<BigIntImmutable>> specializeActualPol(
            final Map<GPolyVar, PolyMatrix<BigIntImmutable>> oldMap,
            final Map<GPolyVar, BigIntImmutable> substitution,
            final BigIntImmutable defaultValue) {

        Map<GPolyVar, PolyMatrix<BigIntImmutable>> newMap =
            new LinkedHashMap<GPolyVar, PolyMatrix<BigIntImmutable>>();
        for (Map.Entry<GPolyVar, PolyMatrix<BigIntImmutable>> monomial : oldMap.entrySet()) {
            PolyMatrix<BigIntImmutable> oldCoeff = monomial.getValue();
            List<List<OrderPoly<BigIntImmutable>>> newEntries =
                new ArrayList<List<OrderPoly<BigIntImmutable>>>(oldCoeff.numRows());
            for (int i = 0; i < oldCoeff.numRows(); i++) {
                List<OrderPoly<BigIntImmutable>> newRow =
                    new ArrayList<OrderPoly<BigIntImmutable>>(oldCoeff.numCols());
                for (int j = 0; j < oldCoeff.numCols(); j++) {
                    OrderPoly<BigIntImmutable> oldEntry = oldCoeff.at(i, j);
                    GPoly<BigIntImmutable, GPolyVar> oldEntryInner = oldEntry.getInnerPoly();
                    BigIntImmutable newEntryCoeff;
                    if (oldEntryInner.containsVariable()) {
                        GPolyVar var = oldEntryInner.getVariables().iterator().next();
                        if (substitution.containsKey(var)) {
                            newEntryCoeff = substitution.get(var);
                        } else {
                            newEntryCoeff = oldEntryInner.getCoeffs().get(0);
                        }
                    } else {
                        newEntryCoeff = defaultValue;
                    }
                    GPoly<BigIntImmutable, GPolyVar> newEntryInner =
                        this.entryPolyFactory.getInnerFactory().buildFromCoeff(newEntryCoeff);
                    OrderPoly<BigIntImmutable> newEntry = this.entryPolyFactory.buildFromCoeff(newEntryInner);
                    newRow.add(newEntry);
                }
                newEntries.add(newRow);
            }
            PolyMatrix<BigIntImmutable> newCoeff = new PolyMatrix<BigIntImmutable>(newEntries);
            newMap.put(monomial.getKey(), newCoeff);
        }
        return newMap;
    }
}
