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
import aprove.xml.*;

/**
 * A PolyMatrixInterpretation for exotic matrices,
 * i.e. matrices containing arctic or tropical numbers.
 *
 * Note on extended monotonicity:
 * The strict greater relation must be monotone in addition to
 * the weak one. This is made sure by enforcing that the first entries of each
 * non-constant coefficient matrix are nonzero, and all entries of each
 * constant coefficient are zero.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ExoticPolyMatrixInterpretation<T extends ExoticInt<T>> extends AbstractPolyMatrixInterpretation<T> {

    /**
     * The minimum coeff value. Determines whether to use Below Zero methods.
     */
    private final T minValue;

    /**
     * A factory for the specific type of exotic numbers we're working with.
     */
    private final ExoticIntFactory<T> intFactory;

    /**
     * The coefficients that are placed in the first component of any vector/matrix.
     * Required for some coeff types where additional restrictions are imposed
     * on the first components that have to be reflected in the binarization.
     */
    protected Set<Set<String>> firstComponentCoeffNames =
        new LinkedHashSet<Set<String>>();

    /**
     * The first entries of the constant coefficients of the interpretations.
     * Required for some coeff types where additional restrictions are imposed
     * on these entries that have to be reflected in the binarization.
     */
    protected Set<String> firstComponentConstantNames =
        new LinkedHashSet<String>();

    private ExoticPolyMatrixInterpretation(
            final Semiring<T> ringC,
            final FlatteningVisitor<GPoly<T, GPolyVar>, GPolyVar> fv,
            final OrderPolyFactory<T> coeffPolyFactory,
            final PolyMatrixFactory<T> matrixFactory,
            final ConstraintFactory<T> constraintFactory,
            final ExoticIntFactory<T> intFactory,
            final T minValue,
            final int dimension,
            final boolean allstrict,
            final Set<FunctionSymbol> collapsingSyms,
            final String description,
            final List<Citation> citations) {
        super(ringC, coeffPolyFactory, matrixFactory, constraintFactory, fv,
                dimension, allstrict, collapsingSyms,
                description, citations);
        this.minValue = minValue;
        this.intFactory = intFactory;
        this.matroType = "arctic";
        this.xmlOptions.put(XMLAttribute.BELOW_ZERO,
                (minValue.signum() < 0) ? "true" : "false");
    }

    /**
     * Create an abstract exotic matrix interpretation with a lower and
     * upper bound for coeff values. If the lower bound is < 0, use
     * 'below zero' mode, otherwise not.
     */
    public static <T extends ExoticInt<T>> ExoticPolyMatrixInterpretation<T> create(
            final Iterable<Constraint<TRSTerm>> constraints,
            final Semiring<T> ringC,
            final FlatteningVisitor<GPoly<T, GPolyVar>, GPolyVar> fv,
            final OrderPolyFactory<T> coeffPolyFactory,
            final PolyMatrixFactory<T> matrixFactory,
            final ConstraintFactory<T> constraintFactory,
            final ExoticIntFactory<T> intFactory,
            final T minValue,
            final int dimension,
            final boolean allstrict,
            final Set<FunctionSymbol> collapsingSyms,
            final String description,
            final List<Citation> citations) {
        ExoticPolyMatrixInterpretation<T> interpretation =
            new ExoticPolyMatrixInterpretation<T>(ringC, fv, coeffPolyFactory,
                    matrixFactory, constraintFactory, intFactory, minValue,
                    dimension, allstrict, collapsingSyms, description, citations);
        for (Constraint<TRSTerm> constraint : constraints) {
            interpretation.extend(constraint);
        }
        return interpretation;
    }

    /**
     * Create an abstract arctic matrix interpretation with lower bound 0,
     * i.e. using arctic natural numbers only.
     */
    public static <T extends ExoticInt<T>> ExoticPolyMatrixInterpretation<T> create(
            final Iterable<Constraint<TRSTerm>> constraints,
            final Semiring<T> ringC,
            final FlatteningVisitor<GPoly<T, GPolyVar>, GPolyVar> fv,
            final OrderPolyFactory<T> coeffPolyFactory,
            final PolyMatrixFactory<T> matrixFactory,
            final ConstraintFactory<T> constraintFactory,
            final ExoticIntFactory<T> intFactory,
            final int dimension,
            final boolean allstrict,
            final Set<FunctionSymbol> collapsingSyms,
            final String description,
            final List<Citation> citations) {
        ExoticPolyMatrixInterpretation<T> interpretation =
            new ExoticPolyMatrixInterpretation<T>(ringC, fv, coeffPolyFactory,
                    matrixFactory, constraintFactory, intFactory, ringC.one(),
                    dimension, allstrict, collapsingSyms, description, citations);
        for (Constraint<TRSTerm> constraint : constraints) {
            interpretation.extend(constraint);
        }
        return interpretation;
    }

    @Override
    public Triple<PolyMatrix<T>, Map<GPolyVar, PolyMatrix<T>>,
                Map<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<T>>>
            getMatrixFromFunction(final FunctionSymbol symbol, boolean collapse) {

        final int arity = symbol.getArity();
        final T factor = this.minValue.signum() < 0 ? this.minValue : null;

        String constantAddendName = this.getNextCoeffName();
        PolyMatrix<T> constantAddend =
            this.matrixFactory.buildCoeffVectorWithFactor(constantAddendName, factor, collapse);
        Set<String> fccs = new LinkedHashSet<String>();
        String constantFCC = constantAddendName + "#1";
        fccs.add(constantFCC);
        this.firstComponentConstantNames.add(constantFCC);
        for (int i = 1; i <= this.dimension; i++) {
            OrderPoly<T> entry = this.entryPolyFactory.buildFromInnerVariable(
                    GAtomicVar.createVariable(constantAddendName + "#" + i));
            this.extendedMonotonicityConstraint.add(
                    this.constraintFactory.createWithQuantifier(entry, ConstraintType.EQ));
        }

        // generate variable names
        List<String> variables = new ArrayList<String>(arity);
        for (int i = 0; i < arity; ++i) {
            variables.add(AbstractPolyMatrixInterpretation.VARIABLE_PREFIX + (i + 1));
        }

        PolyMatrix<T> sum = constantAddend;
        Map<GPolyVar, PolyMatrix<T>> actualPol =
            new LinkedHashMap<GPolyVar, PolyMatrix<T>>();
        actualPol.put(null, constantAddend);

        Map<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<T>> usableRuleConstraints =
            new LinkedHashMap<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<T>>();

        for (int i = 0; i < arity; i++) {
            String coeffName = this.getNextCoeffName();
            fccs.add(coeffName + "#1");
            sum = this.matrixFactory.plus(sum,
                this.matrixFactory.buildVarCoeffVectorWithFactor(
                        coeffName, variables.get(i), factor, collapse));

            PolyMatrix<T> coeffMatrix =
                this.matrixFactory.buildCoeffMatrixWithFactor(coeffName,
                        factor, collapse);
            actualPol.put(GAtomicVar.createVariable(variables.get(i)), coeffMatrix);

            OrderPoly<T> firstEntry =
                this.entryPolyFactory.buildFromInnerVariable(
                        GAtomicVar.createVariable(coeffName + "#1"));
            this.extendedMonotonicityConstraint.add(
                    this.constraintFactory.createWithQuantifier(
                            firstEntry, ConstraintType.GT));
            // TODO maybe require != zero instead of > 0 for tropical

            // pre-generate usable rules constraints
            Set<OrderPolyConstraint<T>> aConditions =
                this.generateActiveConditions(coeffMatrix);
            //this.generateActiveConditions(coeffName);
            // FIXME: does the refactored version do the trick also BZ?
            // hnf. unfortunately not. gotta require a != -I, not 3 *A a != -I.

            Pair<FunctionSymbol, Integer> protoQAC =
                new Pair<FunctionSymbol, Integer>(symbol, i);
            usableRuleConstraints.put(protoQAC, this.constraintFactory.createOr(aConditions));
        }
        this.firstComponentCoeffNames.add(fccs);

        return new Triple<PolyMatrix<T>, Map<GPolyVar, PolyMatrix<T>>,
                    Map<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<T>>>(
                sum, actualPol, usableRuleConstraints);
    }

    /**
     * Slightly uglier than the code from the parent class. Overridden for
     * below zero. Reason: Coeff matrix may contain, e.g., a * (-2).
     * Must require !(a == ZERO) and not !(a * (-2) == ZERO), though.
     *
     * @param coeffMatrix
     * @return
     */
    @Override
    protected Set<OrderPolyConstraint<T>> generateActiveConditions(PolyMatrix<T> coeffMatrix) {
        int rows = coeffMatrix.numRows();
        int cols = coeffMatrix.numCols();
        Set<OrderPolyConstraint<T>> result =
            new LinkedHashSet<OrderPolyConstraint<T>>(rows * cols);
        OrderPoly<T> zeroPoly = this.entryPolyFactory.buildFromCoeff(
                this.entryPolyFactory.getInnerFactory().buildFromCoeff(
                        this.ringC.zero()));

        for (int j = 0; j < rows; j++) {
            for (int k = 0; k < cols; k++) {
                OrderPoly<T> entryPoly = coeffMatrix.get(j, k);
                Set<GPolyVar> coeffs = entryPoly.getInnerVariables();
                if (Globals.useAssertions) {
                    assert coeffs.size() == 1;
                }
                GPolyVar theVar = coeffs.iterator().next();
                OrderPoly<T> unshiftedCoeffPoly = this.entryPolyFactory.buildFromInnerVariable(theVar);
                result.add(this.constraintFactory.createNot(
                        this.constraintFactory.createWithQuantifier(
                        unshiftedCoeffPoly, zeroPoly, ConstraintType.EQ)));
            }
        }
        return result;
    }


    @Override
    public OrderPolyConstraint<T> fromTermConstraints(
            final Collection<Constraint<TRSTerm>> constraints,
            Abortion aborter) throws AbortionException {

        // Step 1: Generate matrix interpretations for the terms and
        // break down the matrix constraints to polynomial ones by
        // pairwise comparison of entries.

        // All pairs have to be oriented at least weakly.
        Set<Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType>> weakConditions =
            new LinkedHashSet<Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType>>();
        // One pair has to be oriented strictly (unless ALLSTRICT is enabled,
        // in which case all pairs have to be oriented strictly)
        Set<Set<Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType>>> strongConditions =
            new LinkedHashSet<Set<Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType>>>();

        for (Constraint<TRSTerm> constraint : constraints) {
            aborter.checkAbortion();
            TermPair tp = TermPair.create(constraint.x, constraint.y);
            PolyMatrix<T> leftMatrix =
                this.interpretTerm(tp.getLhsInStandardRepresentation(), aborter);
            PolyMatrix<T> rightMatrix =
                this.interpretTerm(tp.getRhsInStandardRepresentation(), aborter);
            OrderRelation rel = constraint.z;
            ConstraintType ct = ConstraintType.fromRelation(rel, this.allstrict);

            Set<Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType>> newStrongCond =
                new LinkedHashSet<Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType>>();

            final int numberOfComponents = leftMatrix.numRows();
            for (int i = 0; i < numberOfComponents; i++) {
                aborter.checkAbortion();
                OrderPoly<T> shiftedLeftPoly, shiftedRightPoly;
                if (!this.minValue.isPositive()) {
                    Pair<OrderPoly<T>, OrderPoly<T>> shiftedPolys =
                        this.shift(leftMatrix.at(i, 0), rightMatrix.at(i, 0));
                    shiftedLeftPoly = shiftedPolys.x;
                    shiftedRightPoly = shiftedPolys.y;
                } else {
                    shiftedLeftPoly = leftMatrix.at(i, 0);
                    shiftedRightPoly = rightMatrix.at(i, 0);
                }

                weakConditions.add(
                    new Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType>(
                        shiftedLeftPoly, shiftedRightPoly, ct));
                if (rel == OrderRelation.GR && !this.allstrict) {
                    newStrongCond.add(
                        new Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType>(
                            shiftedLeftPoly, shiftedRightPoly, ConstraintType.GT));
                }
            }
            if (!newStrongCond.isEmpty()) {
                strongConditions.add(newStrongCond);
            }
        }

        // Step 2: Apply the absolute positiveness criterion to the
        // constraints, eg. reducing ax+b > cx+d to a>c && b>d

        Set<OrderPolyConstraint<T>> result =
            new LinkedHashSet<OrderPolyConstraint<T>>();

        for (Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType> cond : weakConditions) {
            result.addAll(this.transformConstraint(cond, aborter));
        }
        if (!strongConditions.isEmpty()) {
            Set<OrderPolyConstraint<T>> strongCond =
                new LinkedHashSet<OrderPolyConstraint<T>>();
            for (Set<Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType>> condSet : strongConditions) {
                aborter.checkAbortion();
                Set<OrderPolyConstraint<T>> smallStrongCond =
                    new LinkedHashSet<OrderPolyConstraint<T>>();
                if (!condSet.isEmpty()) {
                    for (Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType> cond : condSet) {
                        smallStrongCond.add(this.constraintFactory.createAnd(this.transformConstraint(cond, aborter)));
                    }
                    strongCond.add(this.constraintFactory.createAnd(smallStrongCond));
                }
            }
            result.add(this.constraintFactory.createOr(strongCond));
        }

        OrderPolyConstraint<T> resultConstraint =
            this.constraintFactory.createAnd(result);
        resultConstraint = this.constraintFactory.createQuantifierE(
                resultConstraint, resultConstraint.getFreeVariables());
        return resultConstraint;
    }

    protected Set<OrderPolyConstraint<T>> transformConstraint(
            final Triple<OrderPoly<T>, OrderPoly<T>, ConstraintType> constraint,
            Abortion aborter) throws AbortionException {

        OrderPoly<T> leftPoly = constraint.x;
        OrderPoly<T> rightPoly = constraint.y;
        ConstraintType ct = constraint.z;

        VarPartNode<GPolyVar> varOne =
            this.entryPolyFactory.getInnerFactory().getVarOne();
        OrderPoly<T> zeroPoly = this.entryPolyFactory.concat(
                this.entryPolyFactory.getInnerFactory().buildFromCoeff(this.ringC.zero()),
                varOne);

        Set<OrderPolyConstraint<T>> result =
            new LinkedHashSet<OrderPolyConstraint<T>>();

        // Flatten the *outer* polynomials (not the inner ones)
        aborter.checkAbortion();
        leftPoly.visit(this.fvOuter);
        aborter.checkAbortion();
        rightPoly.visit(this.fvOuter);
        aborter.checkAbortion();
        Map<GMonomial<GPolyVar>, GPoly<T, GPolyVar>> leftMonomials =
            leftPoly.getMonomials(this.fvOuter.getRingC(), this.fvOuter.getMonoid());
        Map<GMonomial<GPolyVar>, GPoly<T, GPolyVar>> rightMonomials =
            rightPoly.getMonomials(this.fvOuter.getRingC(), this.fvOuter.getMonoid());
        for (GMonomial<GPolyVar> varPart : leftMonomials.keySet()) {
            aborter.checkAbortion();
            GPoly<T, GPolyVar> leftCoeff = leftMonomials.get(varPart);
            GPoly<T, GPolyVar> rightCoeff = rightMonomials.get(varPart);
            OrderPoly<T> newLeftPoly = this.entryPolyFactory.concat(leftCoeff, varOne);
            // If rightCoeff is a MinusNode, it must be -{[1], [1]}, i.e. 0.
            // Note that the constant part is represented in all polys, even if
            // it is zero.
            if (rightCoeff == null || rightCoeff instanceof MinusNode) {
                result.add(this.constraintFactory.createWithQuantifier(newLeftPoly, zeroPoly, ct));
            } else {
                OrderPoly<T> newRightPoly = this.entryPolyFactory.concat(rightCoeff, varOne);
                result.add(this.constraintFactory.createWithQuantifier(newLeftPoly, newRightPoly, ct));
            }
        }
        // Now check for monomials on the right side which have no corresponding
        // VarPart on the left.
        for (GMonomial<GPolyVar> varPart : rightMonomials.keySet()) {
            aborter.checkAbortion();
            if (!leftMonomials.containsKey(varPart)) {
                OrderPoly<T> newRightPoly = this.entryPolyFactory.concat(
                        rightMonomials.get(varPart), varOne);
                result.add(this.constraintFactory.createWithQuantifier(zeroPoly, newRightPoly, ct));
            }
        }
        return result;
    }

    protected Pair<OrderPoly<T>, OrderPoly<T>> shift(
            final OrderPoly<T> leftPoly,
            final OrderPoly<T> rightPoly) {

        ArcticPolyOffsetVisitor.OuterVisitor<T> offsetVisitor =
            ArcticPolyOffsetVisitor.getVisitor();

        leftPoly.unwrap().visit(offsetVisitor);
        int leftOffset = offsetVisitor.getOffset();
        Map<GPoly<GPoly<T, GPolyVar>, GPolyVar>, Integer> leftRequiredOffsets =
            offsetVisitor.getOffsetMap();
        offsetVisitor.reset();
        rightPoly.unwrap().visit(offsetVisitor);
        int rightOffset = offsetVisitor.getOffset();
        Map<GPoly<GPoly<T, GPolyVar>, GPolyVar>, Integer> rightRequiredOffsets =
            offsetVisitor.getOffsetMap();
        if (Globals.DEBUG_ULRICHSG || Globals.DEBUG_FUHS) {
            /*
            System.err.println("*** Left offset is " + leftOffset + " for " + leftPoly);
            System.err.println("*** Right offset is " + rightOffset + " for " + rightPoly);
            */
        }

        int offset = Math.max(leftOffset, rightOffset);

        ArcticPolyShifter.OuterShifter<T> leftShifter =
            new ArcticPolyShifter.OuterShifter<T>(
                    offset,
                    leftRequiredOffsets,
                    this.entryPolyFactory.getFactory(),
                    this.entryPolyFactory.getInnerFactory(),
                    this.intFactory);

        OrderPoly<T> shiftedLeftPoly =
            new OrderPoly<T>(leftShifter.applyTo(leftPoly.unwrap()));

        ArcticPolyShifter.OuterShifter<T> rightShifter =
            new ArcticPolyShifter.OuterShifter<T>(
                    offset,
                    rightRequiredOffsets,
                    this.entryPolyFactory.getFactory(),
                    this.entryPolyFactory.getInnerFactory(),
                    this.intFactory);
        OrderPoly<T> shiftedRightPoly =
            new OrderPoly<T>(rightShifter.applyTo(rightPoly.unwrap()));
        if (Globals.DEBUG_ULRICHSG || Globals.DEBUG_FUHS) {
            /*
            System.err.println("*** Using offset " + offset);
            System.err.println("*** Left side " + leftPoly + "\nshifted to " + shiftedLeftPoly);
            System.err.println("*** Right side " + rightPoly + "\nshifted to " + shiftedRightPoly);
            */
        }
        return new Pair<OrderPoly<T>, OrderPoly<T>>(
                shiftedLeftPoly, shiftedRightPoly);
    }

    public ExoticPolyMatrixInterpretation<T> specialize(
            final Map<GPolyVar, T> state,
            final T defValue,
            Abortion aborter) throws AbortionException {

        ExoticPolyMatrixInterpretation<T> specialization =
            new ExoticPolyMatrixInterpretation<T>(this.ringC, this.fvOuter,
                    this.entryPolyFactory, this.matrixFactory, this.constraintFactory,
                    this.intFactory, this.minValue, this.dimension, this.allstrict,
                    this.collapsingSyms, this.description, this.citations);
        // make sure not to lose any data here!!!
        specialization.usableRuleConstraints = this.usableRuleConstraints;

        Map<GPolyVar, T> newState = new LinkedHashMap<GPolyVar, T>(state);

        for (Entry<FunctionSymbol, PolyMatrix<T>> entry : this.pol.entrySet()) {
            aborter.checkAbortion();
            PolyMatrix<T> matrix = entry.getValue();
            List<List<OrderPoly<T>>> newEntries =
                new ArrayList<List<OrderPoly<T>>>(matrix.numRows());
            for (int i = 0; i < matrix.numRows(); i++) {
                List<OrderPoly<T>> newRow =
                    new ArrayList<OrderPoly<T>>(matrix.numCols());
                for (int j = 0; j < matrix.numCols(); j++) {
                    OrderPoly<T> poly = matrix.at(i, j);

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
            PolyMatrix<T> newMatrix = new PolyMatrix<T>(newEntries);
            specialization.pol.put(entry.getKey(), newMatrix);
        }
        specialization.model = newState;

        // also specialize the "visual" representation in actualPol
        for (Entry<FunctionSymbol, Map<GPolyVar, PolyMatrix<T>>> entry : this.actualPol.entrySet()) {
            aborter.checkAbortion();
            specialization.actualPol.put(entry.getKey(), this.specializeActualPol(
                    entry.getValue(), state, defValue));
        }
        return specialization;
    }

    protected Map<GPolyVar, PolyMatrix<T>> specializeActualPol(
            final Map<GPolyVar, PolyMatrix<T>> oldMap,
            final Map<GPolyVar, T> substitution,
            final T defaultValue) {

        Map<GPolyVar, PolyMatrix<T>> newMap =
            new LinkedHashMap<GPolyVar, PolyMatrix<T>>();
        for (Map.Entry<GPolyVar, PolyMatrix<T>> monomial : oldMap.entrySet()) {
            PolyMatrix<T> oldCoeff = monomial.getValue();
            List<List<OrderPoly<T>>> newEntries =
                new ArrayList<List<OrderPoly<T>>>(oldCoeff.numRows());
            for (int i = 0; i < oldCoeff.numRows(); i++) {
                List<OrderPoly<T>> newRow =
                    new ArrayList<OrderPoly<T>>(oldCoeff.numCols());
                for (int j = 0; j < oldCoeff.numCols(); j++) {
                    OrderPoly<T> oldEntry = oldCoeff.at(i, j);
                    GPoly<T, GPolyVar> oldEntryInner = oldEntry.getInnerPoly();
                    T newEntryCoeff;
                    if (oldEntryInner.containsVariable()) {
                        GPolyVar var = oldEntryInner.getVariables().iterator().next();
                        if (substitution.containsKey(var)) {
                            // Undo shift here, as the variables in actualPol have no shifting
                            // factor (as opposed to those in pol, where the shifting is
                            // automatically undone during specialization).
                            newEntryCoeff = substitution.get(var).times(this.minValue);
                        } else {
                            newEntryCoeff = oldEntryInner.getCoeffs().get(0);
                        }
                    } else {
                        newEntryCoeff = defaultValue;
                    }
                    GPoly<T, GPolyVar> newEntryInner =
                        this.entryPolyFactory.getInnerFactory().buildFromCoeff(newEntryCoeff);
                    OrderPoly<T> newEntry = this.entryPolyFactory.buildFromCoeff(newEntryInner);
                    newRow.add(newEntry);
                }
                newEntries.add(newRow);
            }
            PolyMatrix<T> newCoeff = new PolyMatrix<T>(newEntries);
            newMap.put(monomial.getKey(), newCoeff);
        }
        return newMap;
    }

    public Set<Set<String>> getFirstComponentCoeffNames() {
        return this.firstComponentCoeffNames;
    }

    public Set<String> getFirstComponentConstantNames() {
        return this.firstComponentConstantNames;
    }
}
