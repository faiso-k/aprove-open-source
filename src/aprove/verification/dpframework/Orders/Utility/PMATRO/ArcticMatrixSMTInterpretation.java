package aprove.verification.dpframework.Orders.Utility.PMATRO;

import java.util.*;
import java.util.Map.Entry;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;
import aprove.verification.oldframework.Algebra.PolyMatrices.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This class is currently not functional.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ArcticMatrixSMTInterpretation { // extends AbstractPolyMatrixInterpretation<ArcticInt> {

    /**
     * The mapping from function symbols to their interpretations.
     * Each interpretation is automatically collapsed to a
     * single column vector with polynomials as entries.
     */
    protected final Map<FunctionSymbol, PolyMatrix<ArcticInt>> pol;

    /**
     * The mapping from function symbols to the "pure" polynomial form
     * of their interpretations (effectively, a sum of matrix*var
     * monomials). Only used for displaying.
     */
    protected final Map<FunctionSymbol, Map<GPolyVar, PolyMatrix<ArcticInt>>> actualPol;

    /**
     * The usable rule constraints will be pre-generated and cached here
     * because constructing them at a later point in time would require
     * lots of unnecessary digging in structures that have been dealt with before.
     */
    protected Map<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<ArcticInt>> usableRuleConstraints;
    protected Map<Pair<FunctionSymbol, Integer>, String> yicesUsableRuleConstraints;

    /**
     * A flattening visitor to operate on outer polynomials.
     */
    protected final FlatteningVisitor<GPoly<ArcticInt, GPolyVar>, GPolyVar> fvOuter;

    /**
     * A factory for matrix entries, which are arctic polynomials.
     */
    protected final OrderPolyFactory<ArcticInt> entryPolyFactory;

    /**
     * A factory for matrices whose entries are arctic polynomials.
     */
    protected final PolyMatrixFactory<ArcticInt> matrixFactory;

    protected final ConstraintFactory<ArcticInt> constraintFactory;

    /**
     * A variable substitution. This is populated by specialize()
     * and holds the matrix entries' actual values as computed
     * by, e.g., a SAT solver.
     */
    protected Map<GPolyVar, ArcticInt> model = null;

    /**
     * The names of all variables occurring in the interpretation.
     * These must be positive or infinite in above-zero interpretations.
     */
    protected final Set<String> varNames;

    protected final Map<String, String> yicesVarNames = new LinkedHashMap<String, String>();

    /**
     * The coefficients that are placed in the first component of any vector/matrix.
     * For every polynomial function, one of these has to be positive in
     * above-zero interpretations ("somewhere finiteness").
     */
    protected Set<Set<String>> firstComponentCoeffNames;

    /**
     * The first entries of the constant coefficients of the interpretations.
     * These have to be positive in below-zero interpretations.
     */
    protected Set<String> firstComponentConstantNames;

    protected Set<String> assertions = new LinkedHashSet<String>();

    /** The dimension of the matrices. */
    protected final int dimension;

    /** Whether to use integers or natural numbers only. */
    protected final boolean belowZero;

    protected final YicesVarFactory yvFactory = new YicesVarFactory();
    protected final YicesCommandFactory ycFactory = new YicesCommandFactory(this.yvFactory);

    /**
     * If true, all pairs have to be oriented strictly. Otherwise, only one has
     * to be oriented strictly while all others have to be oriented weakly.
     */
    protected final boolean allstrict;

    protected ArcticMatrixSMTInterpretation(final int dimension, final boolean belowZero, final boolean allstrict) {

        /*super(ArcticSemiring.create(),
                final OrderPolyFactory<C> entryPolyFactory,
                final PolyMatrixFactory<C> matrixFactory,
                final ConstraintFactory<C> constraintFactory,
                final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter,
                final int dimension,
                final boolean allstrict,
                final String description,
                final List<Citation> citations);*/
        this.dimension = dimension;
        this.belowZero = belowZero;
        this.allstrict = allstrict;
        this.pol = new LinkedHashMap<FunctionSymbol, PolyMatrix<ArcticInt>>();
        this.actualPol = new LinkedHashMap<FunctionSymbol, Map<GPolyVar, PolyMatrix<ArcticInt>>>();
        this.firstComponentCoeffNames = new HashSet<Set<String>>();
        this.firstComponentConstantNames = new HashSet<String>();
        this.varNames = new HashSet<String>();
        this.usableRuleConstraints = new LinkedHashMap<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<ArcticInt>>();
        this.yicesUsableRuleConstraints = new LinkedHashMap<Pair<FunctionSymbol, Integer>, String>();
        final GPolyFactory<ArcticInt, GPolyVar> matrixPolyFactory = new FullSharingFactory<ArcticInt, GPolyVar>();
        this.entryPolyFactory =
            new OrderPolyFactory<ArcticInt>(new FullSharingFactory<GPoly<ArcticInt, GPolyVar>, GPolyVar>(),
                matrixPolyFactory);
        this.matrixFactory = new PolyMatrixFactory<ArcticInt>(this.entryPolyFactory, dimension);
        this.constraintFactory = new SimpleFactory<ArcticInt>();
        this.fvOuter =
            new FlatteningVisitor<GPoly<ArcticInt, GPolyVar>, GPolyVar>(
                new SimpleGPolyFlatRing<GPoly<ArcticInt, GPolyVar>, GPolyVar>(matrixPolyFactory,
                    new GMonomialMonoid<GPolyVar>()));
        assert (false) : "This class should not be used right now.";
    }

    public static ArcticMatrixSMTInterpretation create(final Iterable<Constraint<TRSTerm>> constraints,
        final int dimension,
        final boolean belowZero,
        final boolean allstrict) {

        final ArcticMatrixSMTInterpretation interpretation =
            new ArcticMatrixSMTInterpretation(dimension, belowZero, allstrict);
        for (final Constraint<TRSTerm> constraint : constraints) {
            interpretation.extend(constraint);
        }
        return interpretation;
    }

    public static final String VARIABLE_PREFIX = "x_";
    public static final String ENTRY_PREFIX = "a_";
    public static final String ACTIVE_PREFIX = "b_";
    private int nextEntry;

    /**
     * Returns the name of the next available coefficient identifier.
     * The result is used for /all/ entries of a matrix/vector by
     * the matrix factory, which must add indexes to the name.
     */
    protected String getNextCoeffName() {
        return ArcticMatrixSMTInterpretation.ENTRY_PREFIX + (this.nextEntry++);
    }

    /**
     * Generate an interpretaton for the given symbol if it does
     * not already have one.
     */
    public void extend(final FunctionSymbol symbol) {
        if (!this.pol.containsKey(symbol)) {
            this.buildMatrixFromFunction(symbol);
        }
    }

    /**
     * Generate interpretations for the function symbols occurring
     * in the given constraint.
     */
    public void extend(final Constraint<TRSTerm> constraint) {
        for (final FunctionSymbol fSym : constraint.getLeft().getFunctionSymbols()) {
            this.extend(fSym);
        }
        for (final FunctionSymbol fSym : constraint.getRight().getFunctionSymbols()) {
            this.extend(fSym);
        }
    }

    public Triple<PolyMatrix<ArcticInt>, Map<GPolyVar, PolyMatrix<ArcticInt>>, Map<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<ArcticInt>>> getMatrixFromFunction(final FunctionSymbol symbol) {
        return null;
    }

    public void buildMatrixFromFunction(final FunctionSymbol symbol) {

        final int arity = symbol.getArity();

        final String constantAddendName = this.getNextCoeffName();
        final PolyMatrix<ArcticInt> constantAddend = this.matrixFactory.buildCoeffVector(constantAddendName, false);
        final Set<String> fccs = new LinkedHashSet<String>();
        final String constantFCC = constantAddendName + "#1";
        fccs.add(constantFCC);
        this.firstComponentConstantNames.add(constantFCC);
        for (int i = 1; i <= this.dimension; i++) {
            this.varNames.add(constantAddendName + "#" + i);
        }

        // generate variable names
        final List<String> variables = new ArrayList<String>(arity);
        for (int i = 0; i < arity; ++i) {
            variables.add(ArcticMatrixSMTInterpretation.VARIABLE_PREFIX + (i + 1));
        }

        PolyMatrix<ArcticInt> sum = constantAddend;
        final Map<GPolyVar, PolyMatrix<ArcticInt>> actualPol = new LinkedHashMap<GPolyVar, PolyMatrix<ArcticInt>>();
        actualPol.put(null, constantAddend);

        for (int i = 0; i < arity; i++) {
            final String coeffName = this.getNextCoeffName();
            fccs.add(coeffName + "#1");
            for (int j = 1; j <= this.dimension * this.dimension; j++) {
                this.varNames.add(coeffName + "#" + j);
            }
            sum =
                this.matrixFactory.plus(sum, this.matrixFactory.buildVarCoeffVector(coeffName, variables.get(i), false));

            final PolyMatrix<ArcticInt> coeffMatrix = this.matrixFactory.buildCoeffMatrix(coeffName, false);
            actualPol.put(GAtomicVar.createVariable(variables.get(i)), coeffMatrix);

            // pre-generate usable rules constraints
            final String yicesConditions = this.generateYicesActiveConditions(coeffName);
            final Set<OrderPolyConstraint<ArcticInt>> aConditions = this.generateActiveConditions(coeffName);
            final Pair<FunctionSymbol, Integer> protoQAC = new Pair<FunctionSymbol, Integer>(symbol, i);
            this.usableRuleConstraints.put(protoQAC, this.constraintFactory.createOr(aConditions));
            this.yicesUsableRuleConstraints.put(protoQAC, yicesConditions);
        }
        this.firstComponentCoeffNames.add(fccs);

        this.pol.put(symbol, sum);
        this.actualPol.put(symbol, actualPol);
    }

    /**
     * Create a set of active rule conditions for a given coeff.
     * A rule with a QAC of (f/n) is usable iff the n-th argument of f has
     * a coefficient that is somewhere non-zero.
     * @param coeffName The name of a (matrix) coefficient.
     * @return A constraint that expresses that some entry of the matrix
     * is greater than 0.
     */
    public Set<OrderPolyConstraint<ArcticInt>> generateActiveConditions(final String coeffName) {

        final Set<OrderPolyConstraint<ArcticInt>> result =
            new LinkedHashSet<OrderPolyConstraint<ArcticInt>>(this.dimension * this.dimension);
        final OrderPoly<ArcticInt> zeroPoly =
            this.entryPolyFactory.buildFromCoeff(this.entryPolyFactory.getInnerFactory().buildFromCoeff(ArcticInt.ZERO));

        for (int j = 0; j < this.dimension; j++) {
            for (int k = 0; k < this.dimension; k++) {
                final String entryName = coeffName + "#" + (j * this.dimension + k + 1);
                final OrderPoly<ArcticInt> entryPoly =
                    this.entryPolyFactory.buildFromInnerVariable(GAtomicVar.createVariable(entryName));
                result.add(this.constraintFactory.createWithQuantifier(entryPoly, zeroPoly, ConstraintType.GT));
            }
        }
        return result;
    }

    /**
     * Create a set of active rule conditions for a given coeff.
     * A rule with a QAC of (f/n) is usable iff the n-th argument of f has
     * a coefficient that is somewhere non-zero.
     * @param coeffName The name of a (matrix) coefficient.
     * @return A constraint that expresses that some entry of the matrix
     * is greater than 0.
     */
    public String generateYicesActiveConditions(final String coeffName) {

        final StringBuilder sb = new StringBuilder("(or");

        for (int j = 0; j < this.dimension; j++) {
            for (int k = 0; k < this.dimension; k++) {
                final String entryName = coeffName + "#" + (j * this.dimension + k + 1);
                sb.append(" (not (select ");
                sb.append(entryName);
                sb.append(" 1))");
            }
        }
        sb.append(")");
        return sb.toString();
    }

    /**
     * Interprets the given term as a matrix of polynomials.
     */
    public PolyMatrix<ArcticInt> interpretTerm(final TRSTerm t, final Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert ((t instanceof TRSFunctionApplication) || (t instanceof TRSVariable));
            // if other terms should ever be created, the below code
            // needs to be checked
        }
        if (t.isVariable()) { // easy: Variable
            return this.matrixFactory.buildVariableVector(t.getName());
        } else { // FunctionApplication
            // compute the interpretations of the arguments of t ...
            final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
            if (args.isEmpty()) { // fApp is a constant
                return this.pol.get(fApp.getRootSymbol());
            }
            final int size = args.size();
            final Map<GPolyVar, GPoly<GPoly<ArcticInt, GPolyVar>, GPolyVar>> substitution =
                new LinkedHashMap<GPolyVar, GPoly<GPoly<ArcticInt, GPolyVar>, GPolyVar>>(size);
            for (int i = 0; i < size; ++i) {
                aborter.checkAbortion();
                final PolyMatrix<ArcticInt> argMatrix = this.interpretTerm(args.get(i), aborter);
                for (int j = 0; j < this.dimension; j++) {
                    final String argVarString = ArcticMatrixSMTInterpretation.VARIABLE_PREFIX + (i + 1) + "#" + (j + 1);
                    final GPolyVar argVar = GAtomicVar.createVariable(argVarString);
                    substitution.put(argVar, argMatrix.at(j, 0).unwrap());
                }
            }
            // ... then get the interpretation of the root symbol
            final PolyMatrix<ArcticInt> rootMatrix = this.pol.get(fApp.getRootSymbol());
            // and plug the arg polys into the root polys
            return this.matrixFactory.substituteVariables(rootMatrix, substitution, aborter);
        }
    }

    public OrderPolyConstraint<ArcticInt> gfromTermConstraints(final Collection<Constraint<TRSTerm>> constraints) {
        return null;
    }

    public String fromTermConstraints(final Collection<Constraint<TRSTerm>> constraints, final Abortion aborter)
            throws AbortionException {

        // Step 1: Generate matrix interpretations for the terms and
        // break down the matrix constraints to polynomial ones by
        // pairwise comparison of entries.

        // All pairs have to be oriented at least weakly.
        final Set<Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType>> weakConditions =
            new LinkedHashSet<Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType>>();
        // One pair has to be oriented strictly (unless ALLSTRICT is enabled,
        // in which case all pairs have to be oriented strictly)
        final Set<Set<Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType>>> strongConditions =
            new LinkedHashSet<Set<Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType>>>();

        for (final Constraint<TRSTerm> constraint : constraints) {
            aborter.checkAbortion();
            final TermPair tp = TermPair.create(constraint.x, constraint.y);
            final PolyMatrix<ArcticInt> leftMatrix = this.interpretTerm(tp.getLhsInStandardRepresentation(), aborter);
            final PolyMatrix<ArcticInt> rightMatrix = this.interpretTerm(tp.getRhsInStandardRepresentation(), aborter);
            final OrderRelation rel = constraint.z;
            final ConstraintType ct = ConstraintType.fromRelation(rel, this.allstrict);

            final Set<Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType>> newStrongCond =
                new HashSet<Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType>>();

            for (int i = 0; i < this.dimension; i++) {
                aborter.checkAbortion();
                final OrderPoly<ArcticInt> leftPoly = leftMatrix.at(i, 0);
                final OrderPoly<ArcticInt> rightPoly = rightMatrix.at(i, 0);

                weakConditions.add(new Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType>(leftPoly,
                    rightPoly, ct));
                if (rel == OrderRelation.GR && !this.allstrict) {
                    newStrongCond.add(new Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType>(leftPoly,
                        rightPoly, ConstraintType.GT));
                }
            }
            if (!newStrongCond.isEmpty()) {
                strongConditions.add(newStrongCond);
            }
        }

        // Step 2: Apply the absolute positiveness criterion to the
        // constraints, eg. reducing ax+b > cx+d to a>c && b>d

        final StringBuilder sb = new StringBuilder("(and ");

        for (final Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType> cond : weakConditions) {
            aborter.checkAbortion();
            sb.append(this.transformConstraint(cond));
        }

        if (!strongConditions.isEmpty()) {
            sb.append("(or ");
            for (final Set<Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType>> condSet : strongConditions) {
                aborter.checkAbortion();
                if (!condSet.isEmpty()) {
                    sb.append("(and ");
                    for (final Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType> cond : condSet) {
                        sb.append(this.transformConstraint(cond));
                    }
                    sb.append(")");
                }
            }
            sb.append(")");
        }
        sb.append(")");
        return sb.toString();
    }

    protected String transformConstraint(final Triple<OrderPoly<ArcticInt>, OrderPoly<ArcticInt>, ConstraintType> constraint) {

        final OrderPoly<ArcticInt> leftPoly = constraint.x;
        final OrderPoly<ArcticInt> rightPoly = constraint.y;
        final ConstraintType ct = constraint.z;

        final StringBuilder sb = new StringBuilder();

        // Flatten the *outer* polynomials (not the inner ones)
        leftPoly.visit(this.fvOuter);
        rightPoly.visit(this.fvOuter);
        final Map<GMonomial<GPolyVar>, GPoly<ArcticInt, GPolyVar>> leftMonomials =
            leftPoly.getMonomials(this.fvOuter.getRingC(), this.fvOuter.getMonoid());
        final Map<GMonomial<GPolyVar>, GPoly<ArcticInt, GPolyVar>> rightMonomials =
            rightPoly.getMonomials(this.fvOuter.getRingC(), this.fvOuter.getMonoid());
        final ArcticPolyToYicesConverter polyToYices = new ArcticPolyToYicesConverter(this.ycFactory, this.yvFactory);
        for (final GMonomial<GPolyVar> varPart : leftMonomials.keySet()) {
            final GPoly<ArcticInt, GPolyVar> leftCoeff = leftMonomials.get(varPart);
            final GPoly<ArcticInt, GPolyVar> rightCoeff = rightMonomials.get(varPart);

            polyToYices.reset();
            polyToYices.applyTo(leftCoeff);
            final String leftString = polyToYices.getResult();
            String rightString;
            if (rightCoeff == null || rightCoeff instanceof MinusNode) {
                rightString = ArcticInt.ZERO.toYices();
            } else {
                polyToYices.reset();
                polyToYices.applyTo(rightCoeff);
                rightString = polyToYices.getResult();
            }
            final String var = this.yvFactory.createBoolVar();
            sb.append(" ");
            sb.append(var);
            this.assertions.add(this.ycFactory.acompare(var, leftString, rightString, ct));
        }
        // Now check for monomials on the right side which have no corresponding
        // VarPart on the left.
        for (final GMonomial<GPolyVar> varPart : rightMonomials.keySet()) {
            if (!leftMonomials.containsKey(varPart)) {
                final GPoly<ArcticInt, GPolyVar> rightCoeff = rightMonomials.get(varPart);
                final String leftString = ArcticInt.ZERO.toYices();
                polyToYices.reset();
                polyToYices.applyTo(rightCoeff);
                final String rightString = polyToYices.getResult();
                final String var = this.yvFactory.createBoolVar();
                sb.append(" ");
                sb.append(var);
                this.assertions.add(this.ycFactory.acompare(var, leftString, rightString, ct));
            }
        }
        this.assertions.addAll(polyToYices.getAssertions());
        this.yicesVarNames.putAll(polyToYices.getNewVariables());
        return sb.toString();
    }

    public String getActiveRuleConstraints(final Map<? extends GeneralizedRule, QActiveCondition> usableRules, final Abortion aborter)
            throws AbortionException {

        if (usableRules.isEmpty()) {
            return null;
        }

        final StringBuilder sb = new StringBuilder("(and ");

        // extend signature
        for (final GeneralizedRule rule : usableRules.keySet()) {
            for (final FunctionSymbol f : rule.getFunctionSymbols()) {
                this.extend(f);
            }
        }

        // build constraints
        for (final Map.Entry<? extends GeneralizedRule, QActiveCondition> usable : usableRules.entrySet()) {
            final QActiveCondition qac = usable.getValue();
            final GeneralizedRule rule = usable.getKey();
            final Constraint<TRSTerm> ruleConstraint = Constraint.fromRule(rule, OrderRelation.GE);
            final Set<Constraint<TRSTerm>> rcSet = Collections.singleton(ruleConstraint);
            final String polyRuleConstraint = this.fromTermConstraints(rcSet, aborter);
            if (qac != QActiveCondition.TRUE) {
                sb.append("(or (not (or ");
                for (final Set<Pair<FunctionSymbol, Integer>> andCondition : qac.getSetRepresentation()) {
                    sb.append("(and ");
                    for (final Pair<FunctionSymbol, Integer> aCond : andCondition) {
                        sb.append(this.yicesUsableRuleConstraints.get(aCond));
                    }
                    sb.append(")");
                }
                sb.append(")) "); // end of inner "or" and "not"
                // if the constraint from the QACs is fulfilled, then the rule constraint must be, too
                sb.append(polyRuleConstraint);
                sb.append(")"); // end of outer "or"
            } else {
                sb.append(polyRuleConstraint);
            }
        }
        sb.append(")");
        return sb.toString();
    }

    /**
     * Determine whether an Active Rule Condition is satisfied.
     * Can only be used after specialization.
     * @param condition Some QActiveCondition.
     * @param coeffOrder An order to determine whether values are >0.
     * @return true iff the given condition is fulfilled.
     */
    public boolean solvesQActiveConstraint(final QActiveCondition condition, final CoeffOrder<ArcticInt> coeffOrder) {

        if (condition == QActiveCondition.TRUE) {
            return true;
        }
        if (Globals.useAssertions) {
            assert (this.model != null);
        }
        for (final Set<Pair<FunctionSymbol, Integer>> andCondition : condition.getSetRepresentation()) {
            boolean conjunctFulfilled = true;
            for (final Pair<FunctionSymbol, Integer> condAtom : andCondition) {
                final OrderPolyConstraint<ArcticInt> orConstraint = this.usableRuleConstraints.get(condAtom);
                Set<OrderPolyConstraint<ArcticInt>> constraints;
                if (orConstraint instanceof OPCOr) {
                    constraints = ((OPCOr<ArcticInt>) orConstraint).getOperands();
                } else { // if dimension = 1
                    constraints = Collections.singleton(orConstraint);
                    // constraints = new HashSet<OrderPolyConstraint<ArcticInt>>();
                    // constraints.add(orConstraint);
                }
                boolean someCoeffIsPositive = false;
                for (final OrderPolyConstraint<ArcticInt> constraint : constraints) {
                    OrderPolyConstraint<ArcticInt> actualConstraint;
                    if (constraint instanceof OPCQuantifierA) {
                        actualConstraint = ((OPCQuantifierA<ArcticInt>) constraint).getInnerConstraint();
                    } else {
                        actualConstraint = constraint;
                    }
                    if (Globals.useAssertions) {
                        assert (actualConstraint instanceof OPCAtom) : "Error: atom expected, found: "
                            + actualConstraint;
                    }
                    final OrderPoly<ArcticInt> poly = ((OPCAtom<ArcticInt>) actualConstraint).getLeftPoly();
                    final GPolyVar var = poly.getInnerPoly().getVariables().iterator().next();
                    final ArcticInt value = this.model.get(var);
                    if (coeffOrder.isGreater(value, ArcticInt.ZERO)) {
                        someCoeffIsPositive = true;
                    }
                }
                if (!someCoeffIsPositive) {
                    conjunctFulfilled = false;
                }
            }
            if (conjunctFulfilled) {
                return true;
            }
        }
        return false;
    }

    public ArcticMatrixSMTInterpretation specialize(final Map<GPolyVar, ArcticInt> state,
        final ArcticInt defValue,
        final Abortion aborter) throws AbortionException {

        final ArcticMatrixSMTInterpretation specialization =
            new ArcticMatrixSMTInterpretation(this.dimension, this.belowZero, this.allstrict);
        // make sure not to lose any data here!!!
        specialization.usableRuleConstraints = this.usableRuleConstraints;
        specialization.yicesUsableRuleConstraints = this.yicesUsableRuleConstraints;

        final Map<GPolyVar, ArcticInt> newState = new LinkedHashMap<GPolyVar, ArcticInt>(state);

        for (final Entry<FunctionSymbol, PolyMatrix<ArcticInt>> entry : this.pol.entrySet()) {
            final PolyMatrix<ArcticInt> matrix = entry.getValue();
            final List<List<OrderPoly<ArcticInt>>> newEntries =
                new ArrayList<List<OrderPoly<ArcticInt>>>(matrix.numRows());
            for (int i = 0; i < matrix.numRows(); i++) {
                aborter.checkAbortion();
                final List<OrderPoly<ArcticInt>> newRow = new ArrayList<OrderPoly<ArcticInt>>(matrix.numCols());
                for (int j = 0; j < matrix.numCols(); j++) {
                    OrderPoly<ArcticInt> poly = matrix.at(i, j);

                    // replace every variable not in state by defValue
                    for (final GPolyVar var : poly.getInnerVariables()) {
                        if (!newState.containsKey(var)) {
                            newState.put(var, defValue);
                        }
                    }
                    poly = this.deepSubstitute(poly, newState, aborter);
                    newRow.add(poly);
                }
                newEntries.add(newRow);
            }
            final PolyMatrix<ArcticInt> newMatrix = new PolyMatrix<ArcticInt>(newEntries);
            specialization.pol.put(entry.getKey(), newMatrix);
        }
        specialization.model = newState;

        // also specialize the "visual" representation in actualPol
        for (final Entry<FunctionSymbol, Map<GPolyVar, PolyMatrix<ArcticInt>>> entry : this.actualPol.entrySet()) {
            specialization.actualPol.put(entry.getKey(), this.specializeActualPol(entry.getValue(), state, defValue));
        }
        return specialization;
    }

    protected Map<GPolyVar, PolyMatrix<ArcticInt>> specializeActualPol(final Map<GPolyVar, PolyMatrix<ArcticInt>> oldMap,
        final Map<GPolyVar, ArcticInt> substitution,
        final ArcticInt defaultValue) {

        final Map<GPolyVar, PolyMatrix<ArcticInt>> newMap = new LinkedHashMap<GPolyVar, PolyMatrix<ArcticInt>>();
        for (final Map.Entry<GPolyVar, PolyMatrix<ArcticInt>> monomial : oldMap.entrySet()) {
            final PolyMatrix<ArcticInt> oldCoeff = monomial.getValue();
            final List<List<OrderPoly<ArcticInt>>> newEntries =
                new ArrayList<List<OrderPoly<ArcticInt>>>(oldCoeff.numRows());
            for (int i = 0; i < oldCoeff.numRows(); i++) {
                final List<OrderPoly<ArcticInt>> newRow = new ArrayList<OrderPoly<ArcticInt>>(oldCoeff.numCols());
                for (int j = 0; j < oldCoeff.numCols(); j++) {
                    final OrderPoly<ArcticInt> oldEntry = oldCoeff.at(i, j);
                    final GPoly<ArcticInt, GPolyVar> oldEntryInner = oldEntry.getInnerPoly();
                    ArcticInt newEntryCoeff;
                    if (oldEntryInner.containsVariable()) {
                        final GPolyVar var = oldEntryInner.getVariables().iterator().next();
                        if (substitution.containsKey(var)) {
                            // Undo shift here, as the variables in actualPol have no shifting
                            // factor (as opposed to those in pol, where the shifting is
                            // automatically undone during specialization).
                            newEntryCoeff = substitution.get(var);
                        } else {
                            newEntryCoeff = oldEntryInner.getCoeffs().get(0);
                        }
                    } else {
                        newEntryCoeff = defaultValue;
                    }
                    final GPoly<ArcticInt, GPolyVar> newEntryInner =
                        this.entryPolyFactory.getInnerFactory().buildFromCoeff(newEntryCoeff);
                    final OrderPoly<ArcticInt> newEntry = this.entryPolyFactory.buildFromCoeff(newEntryInner);
                    newRow.add(newEntry);
                }
                newEntries.add(newRow);
            }
            final PolyMatrix<ArcticInt> newCoeff = new PolyMatrix<ArcticInt>(newEntries);
            newMap.put(monomial.getKey(), newCoeff);
        }
        return newMap;
    }

    /**
     * Substitute the coefficient variables of a polynomial
     * according to the given map.
     * @param polynomial The polynomial.
     * @param state The map defining the substutution.
     * @return An OrderPoly where the variables inside the
     * coefficients are substituted according to state.
     */
    protected OrderPoly<ArcticInt> deepSubstitute(final OrderPoly<ArcticInt> polynomial,
        final Map<GPolyVar, ArcticInt> state,
        final Abortion aborter) throws AbortionException {
        final Map<GPolyVar, GPoly<ArcticInt, GPolyVar>> subst =
            new LinkedHashMap<GPolyVar, GPoly<ArcticInt, GPolyVar>>(state.size());
        final VarPartNode<GPolyVar> varOne = this.entryPolyFactory.getVarOne();

        // provide a map that can be used for substitutions over GPOLYs.
        for (final Map.Entry<GPolyVar, ArcticInt> entry : state.entrySet()) {
            aborter.checkAbortion();
            final GPolyVar var = entry.getKey();
            final ArcticInt coeff = entry.getValue();
            final GPoly<ArcticInt, GPolyVar> substPoly = this.entryPolyFactory.getInnerFactory().concat(coeff, varOne);
            subst.put(var, substPoly);
        }

        final Map<GPoly<ArcticInt, GPolyVar>, GPoly<ArcticInt, GPolyVar>> coeffMap =
            new LinkedHashMap<GPoly<ArcticInt, GPolyVar>, GPoly<ArcticInt, GPolyVar>>();
        // substitute in each coefficient
        for (final GPoly<ArcticInt, GPolyVar> coeff : polynomial.getCoeffs()) {
            aborter.checkAbortion();
            if (coeff != null) {
                GPoly<ArcticInt, GPolyVar> result = coeff;
                result =
                    this.entryPolyFactory.getInnerFactory().substituteVariables(result, subst, ArcticSemiring.create(),
                        aborter);

                // take care that the new coeff will be used in the final result
                if (!coeff.equals(result)) {
                    coeffMap.put(coeff, result);
                }
            }
        }

        // build a new (outer) polynomial with the new coefficients
        OrderPoly<ArcticInt> result = polynomial;
        for (final Map.Entry<GPoly<ArcticInt, GPolyVar>, GPoly<ArcticInt, GPolyVar>> entry : coeffMap.entrySet()) {
            result = this.entryPolyFactory.substituteCoefficient(result, entry.getKey(), entry.getValue(), null);
        }
        return result;
    }

    /**
     * Build a Yices statement expressing that all variables in the interpretation
     * are positive. This is what distinguishes above-zero interpretations from
     * below-zero ones.
     */
    public String getAboveZeroConstraint() {
        // (assert (= (notNegative x) (or (not (finite x)) (>= (select x 2) 0))))
        final StringBuilder sb = new StringBuilder("(and");
        for (final String var : this.varNames) {
            sb.append(" (or (select ");
            sb.append(var);
            sb.append(" 1) (>= (select ");
            sb.append(var);
            sb.append(" 2) 0))");
        }
        sb.append(")");
        return sb.toString();
    }

    public String getVariableDeclarations() {

        final StringBuilder sb = new StringBuilder();
        for (final String var : this.varNames) {
            sb.append("(define ");
            sb.append(var);
            sb.append("::arctic)\n");
        }
        for (final String yicesVar : this.yvFactory.getArcticVars()) {
            sb.append("(define ");
            sb.append(yicesVar);
            sb.append("::arctic)\n");
        }
        for (final String yicesVar : this.yvFactory.getBoolVars()) {
            sb.append("(define ");
            sb.append(yicesVar);
            sb.append("::bool)\n");
        }
        return sb.toString();
    }

    /**
     * Build a Yices statement expressing the restrictions imposed on variables:
     * For above-zero interpretations, every polynomial function has to be
     * somewhere finite (i.e., one of the coefficients' first entries is finite),
     * for below-zero interpretations, all constant coefficient vectors must have
     * a positive first element.
     */
    public String getFinitenessConstraint() {
        // (assert (= (positive x) (and (finite x) (>= (select x 2) 0))))
        final StringBuilder sb = new StringBuilder("(and");
        if (this.belowZero) {
            for (final String var : this.firstComponentConstantNames) {
                sb.append(" (not (select ");
                sb.append(var);
                sb.append(" 1)) (>= (select ");
                sb.append(var);
                sb.append(" 2) 0)");
            }
        } else {
            for (final Set<String> varNames : this.firstComponentCoeffNames) {
                sb.append(" (or");
                for (final String var : varNames) {
                    sb.append(" (not (select ");
                    sb.append(var);
                    sb.append(" 1) (>= (select ");
                    sb.append(var);
                    sb.append(" 2) 0)");
                }
                sb.append(")");
            }
        }
        sb.append(")");
        return sb.toString();
    }

    public Set<String> getAssertions() {
        final Set<String> result = new LinkedHashSet<String>(this.assertions);
        /*for (Map.Entry<String, String> yicesVar : this.yicesVarNames.entrySet()) {
            result.add("(assert (= " + yicesVar.getKey() + " " + yicesVar.getValue() + "))\n");
        }*/
        return result;
    }

    /**
     * Exports the mapping from function symbols to polynomials with matrix coefficients.
     *
     * @param eu the export util
     * @return the exported version of the interpretation
     */
    public String export(final Export_Util eu) {
        final StringBuilder result = new StringBuilder("Matrix interpretation ");
        result.append(eu.cite(Citation.MATRO));
        result.append(" with arctic ");
        result.append(this.belowZero ? "integers " : " natural numbers ");
        result.append(eu.cite(Citation.ARCTIC));
        result.append(":\n");

        final int size = this.actualPol.size();
        final List<String> rows = new ArrayList<String>(size);

        for (final Map.Entry<FunctionSymbol, Map<GPolyVar, PolyMatrix<ArcticInt>>> entry : this.actualPol.entrySet()) {
            final List<String> rowEntries = new ArrayList<String>();
            final StringBuilder sb = new StringBuilder("POL(");
            final FunctionSymbol functionSymbol = entry.getKey();
            final int arity = functionSymbol.getArity();

            // display function symbol with argument list
            final StringBuilder functionWithVars = new StringBuilder(functionSymbol.export(eu));
            if (arity > 0) {
                functionWithVars.append("(");
                for (int i = 1; i <= arity; ++i) {
                    final String var = ArcticMatrixSMTInterpretation.VARIABLE_PREFIX + i;
                    functionWithVars.append(this.exportVarName(var, eu));
                    if (i < arity) {
                        functionWithVars.append(", ");
                    }
                }
                functionWithVars.append(")");
            }

            // append polynomial interpretation
            sb.append(functionWithVars.toString());
            sb.append(") = ");
            rowEntries.add(sb.toString());
            final Map<GPolyVar, PolyMatrix<ArcticInt>> monomials = entry.getValue();
            int i = 1;
            for (final Map.Entry<GPolyVar, PolyMatrix<ArcticInt>> monomial : monomials.entrySet()) {
                if (monomial.getKey() == null) {
                    rowEntries.add(monomial.getValue().export(eu));
                } else {
                    rowEntries.add(monomial.getValue().export(eu));
                    rowEntries.add(eu.multSign());
                    rowEntries.add(eu.bold(this.exportVarName(monomial.getKey().getName(), eu)));
                }
                if (i < monomials.size()) {
                    rowEntries.add(" + ");
                }
                ++i;
            }
            final StringBuilder line = new StringBuilder();
            line.append(eu.tableStart(rowEntries.size()));
            line.append(eu.tableRow(rowEntries));
            line.append(eu.tableEnd());
            // line.append(eu.linebreak());
            rows.add(line.toString());
        }

        result.append(eu.set(rows, Export_Util.RULES));
        return result.toString();
    }

    protected String exportVarName(final String varName, final Export_Util eu) {
        final String[] elements = varName.split("_");
        String name = elements[0];
        if (elements.length > 1) {
            name += eu.sub(elements[1]);
        }
        return name;
    }

    /**
     * @return a simple string representation.
     */
    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public Element toDOM(final Document doc) {
        throw new UnsupportedOperationException();
    }

    private static class ArcticPolyToYicesConverter extends GPolyVisitor<ArcticInt, GPolyVar> {

        public ArcticPolyToYicesConverter(final YicesCommandFactory ycFactory, final YicesVarFactory yvFactory) {
            super();
            this.ycFactory = ycFactory;
            this.yvFactory = yvFactory;
        }

        private final YicesCommandFactory ycFactory;
        private final YicesVarFactory yvFactory;

        private String yicesExpr = "";

        private final Map<GPoly<ArcticInt, GPolyVar>, String> subExprs =
            new HashMap<GPoly<ArcticInt, GPolyVar>, String>();

        protected Set<String> assertions = new LinkedHashSet<String>();

        protected Map<String, String> freshVariables = new LinkedHashMap<String, String>();

        public String getResult() {
            return this.yicesExpr;
        }

        public void reset() {
            this.yicesExpr = "";
        }

        @Override
        public GPoly<ArcticInt, GPolyVar> applyTo(final GPoly<ArcticInt, GPolyVar> visitable) {
            return super.applyTo(visitable);
        }

        @Override
        public GPoly<ArcticInt, GPolyVar> casePlusNode(final PlusNode<ArcticInt, GPolyVar> node,
            final GPoly<ArcticInt, GPolyVar> left,
            final GPoly<ArcticInt, GPolyVar> right) {

            if (this.subExprs.containsKey(node)) {
                this.yicesExpr = this.subExprs.get(node);
                return node;
            }

            if (Globals.useAssertions) {
                assert (this.subExprs.containsKey(left)) : "No entry found for " + left + ", map is " + this.subExprs;
                assert (this.subExprs.containsKey(right)) : "No entry found for " + right + ", map is " + this.subExprs;
            }

            String result;
            if (this.subExprs.get(left).equals("zero")) {
                result = this.subExprs.get(right);
            } else if (this.subExprs.get(right).equals("zero")) {
                result = this.subExprs.get(left);
            } else {
                final StringBuilder sb = new StringBuilder("(aplus ");
                sb.append(this.subExprs.get(left));
                sb.append(" ");
                sb.append(this.subExprs.get(right));
                sb.append(")");
                result = this.yvFactory.createArcticVar();
                this.assertions.addAll(this.ycFactory.aplus(result, this.subExprs.get(left), this.subExprs.get(right)));
                this.freshVariables.put(result, sb.toString());
            }
            this.subExprs.put(node, result);
            this.yicesExpr = result;
            return node;
        }

        @Override
        public GPoly<ArcticInt, GPolyVar> caseTimesNode(final TimesNode<ArcticInt, GPolyVar> node,
            final GPoly<ArcticInt, GPolyVar> left,
            final GPoly<ArcticInt, GPolyVar> right) {

            if (this.subExprs.containsKey(node)) {
                this.yicesExpr = this.subExprs.get(node);
                return node;
            }

            if (Globals.useAssertions) {
                assert (this.subExprs.containsKey(left)) : "No entry found for " + left + ", map is " + this.subExprs;
                assert (this.subExprs.containsKey(right)) : "No entry found for " + right + ", map is " + this.subExprs;
            }

            String result;
            if (this.subExprs.get(left).equals("one")) {
                result = this.subExprs.get(right);
            } else if (this.subExprs.get(right).equals("one")) {
                result = this.subExprs.get(left);
            } else if (this.subExprs.get(left).equals("zero") || this.subExprs.get(right).equals("zero")) {
                result = "zero";
            } else {
                final StringBuilder sb = new StringBuilder("(atimes ");
                sb.append(this.subExprs.get(left));
                sb.append(" ");
                sb.append(this.subExprs.get(right));
                sb.append(")");
                result = this.yvFactory.createArcticVar();
                this.assertions.add(this.ycFactory.atimes(result, this.subExprs.get(left), this.subExprs.get(right)));
                this.freshVariables.put(result, sb.toString());
            }
            this.subExprs.put(node, result);
            this.yicesExpr = result;
            return node;
        }

        @Override
        public GPoly<ArcticInt, GPolyVar> caseConcatNode(final ConcatNode<ArcticInt, GPolyVar> node) {

            if (this.subExprs.containsKey(node)) {
                this.yicesExpr = this.subExprs.get(node);
                return node;
            }

            String result;
            final ArcticInt coeff = node.getCoeff();
            final VarPartNode<GPolyVar> varPart = node.getVarPartNode();
            if (node.containsVariable()) {
                String vars;
                if (varPart.length() < 2) {
                    vars = varPart.getVariablesWithExponents().keySet().iterator().next().getName();
                } else {
                    final String varTerm = this.transformVarPartNode(varPart);
                    vars = this.yvFactory.createArcticVar();
                    this.freshVariables.put(vars, varTerm);
                }
                if (coeff == null || coeff.equals(ArcticInt.ONE)) {
                    result = vars;
                } else if (!coeff.isFinite()) {
                    result = "zero";
                    this.subExprs.put(node, result);
                    this.yicesExpr = result;
                    return node;
                } else {
                    result = this.yvFactory.createArcticVar();
                    final String expr =
                        this.ycFactory.atimes(result, coeff.toYices(), this.transformVarPartNode(varPart));
                    this.freshVariables.put(result, expr);
                }
            } else { // no variable
                if (coeff == null) {
                    result = "one";
                } else {
                    result = coeff.toYices();
                }
            }
            this.subExprs.put(node, result);
            this.yicesExpr = result;
            return node;
        }

        private String transformVarPartNode(final VarPartNode<GPolyVar> node) {

            final Map<GPolyVar, Integer> vars = node.getVariablesWithExponents();
            if ((vars.size() < 2) && (vars.values().iterator().next() == 1)) {
                // only a single variable in this node
                return vars.keySet().iterator().next().getName();
            } else {
                final List<String> varNames = new ArrayList<String>();
                for (final Map.Entry<GPolyVar, Integer> entry : vars.entrySet()) {
                    for (int i = 0; i < entry.getValue(); i++) {
                        varNames.add(entry.getKey().getName());
                    }
                }
                return this.transformVarNameList(varNames);
            }
        }

        private String transformVarNameList(final List<String> varNames) {

            switch (varNames.size()) {
            case 1:
                return varNames.get(0);
            case 2:
                final String var = this.yvFactory.createArcticVar();
                this.assertions.add(this.ycFactory.atimes(var, varNames.get(0), varNames.get(1)));
                return var;
            default:
                final String var2 = this.yvFactory.createArcticVar();
                final String expr = this.transformVarNameList(varNames.subList(1, varNames.size()));
                this.assertions.add(this.ycFactory.atimes(var2, varNames.get(0), expr));
                return var2;
            }
        }

        public Set<String> getAssertions() {
            return this.assertions;
        }

        public Map<String, String> getNewVariables() {
            return this.freshVariables;
        }
    }

    private static class YicesCommandFactory {

        private final YicesVarFactory yvFactory;

        public YicesCommandFactory(final YicesVarFactory yvFactory) {
            this.yvFactory = yvFactory;
        }

        // (assert (= (finite x) (not(select x 1))))
        private String finite(final String arg) {
            return "(not (select " + arg + " 1))";
        }

        private String infinite(final String arg) {
            return "(select " + arg + " 1)";
        }

        private String value(final String arg) {
            return "(select " + arg + " 2)";
        }

        // (assert (= (notNegative x) (or (not (finite x)) (>= (select x 2) 0))))
        public Set<String> notNegative(final String arg) {

            final StringBuilder sb = new StringBuilder("(assert (= (notNegative ");
            sb.append(arg);
            sb.append(") (or (not (finite ");
            sb.append(arg);
            sb.append(")) (>= ");
            sb.append(this.value(arg));
            sb.append(" 0))))\n");

            final Set<String> result = new LinkedHashSet<String>();
            result.add(sb.toString());
            result.add(this.finite(arg));
            return result;
        }

        // (assert (= (positive x) (and (finite x) (>= (select x 2) 0))))
        public Set<String> positive(final String arg) {

            final StringBuilder sb = new StringBuilder("(assert (= (positive ");
            sb.append(arg);
            sb.append(") (and (finite ");
            sb.append(arg);
            sb.append(") (>= (select ");
            sb.append(arg);
            sb.append(" 2) 0))))\n");

            final Set<String> result = new LinkedHashSet<String>();
            result.add(sb.toString());
            result.add(this.finite(arg));
            return result;
        }

        // (assert (= (agt x y) (or (not (finite y)) (and (finite x) (> (select x 2) (select y 2))))))
        public String agt(final String var, final String left, final String right) {

            final StringBuilder sb = new StringBuilder("(assert (= ");
            sb.append(var);
            sb.append(" (or ");
            sb.append(this.infinite(right));
            sb.append(" (and ");
            sb.append(this.finite(left));
            sb.append(" (> ");
            sb.append(this.value(left));
            sb.append(" ");
            sb.append(this.value(right));
            sb.append(")))))\n");

            return sb.toString();
        }

        // (assert (= (aeq x y) (if (finite x) (and (finite y) (= (select x 2) (select y 2)) (not (finite y))))))
        public String aeq(final String var, final String left, final String right) {

            final StringBuilder sb = new StringBuilder("(assert (= ");
            sb.append(var);
            sb.append(" (if ");
            sb.append(this.finite(left));
            sb.append(" (and ");
            sb.append(this.finite(right));
            sb.append(" (= ");
            sb.append(this.value(left));
            sb.append(" ");
            sb.append(this.value(right));
            sb.append(") (not ");
            sb.append(this.finite(right));
            sb.append(")))))\n");

            return sb.toString();
        }

        // (assert (= (age x y) (if (select x 1) (select y 1) (or (select y 1) (>= (select x 2) (select y 2))))))
        public String age(final String var, final String left, final String right) {

            final StringBuilder sb = new StringBuilder("(assert (= ");
            sb.append(var);
            sb.append(" (if ");
            sb.append(this.infinite(left));
            sb.append(" ");
            sb.append(this.infinite(right));
            sb.append(" (or ");
            sb.append(this.infinite(right));
            sb.append(" (>= ");
            sb.append(this.value(left));
            sb.append(" ");
            sb.append(this.value(right));
            sb.append(")))))\n");

            return sb.toString();
        }

        // (assert (= (max x y)) (if (>= x y) x y))
        public String max(final String left, final String right) {

            final StringBuilder lrb = new StringBuilder(left);
            lrb.append(" ");
            lrb.append(right);
            final String leftRight = lrb.toString();

            final StringBuilder sb = new StringBuilder("(assert (= (max ");
            sb.append(leftRight);
            sb.append(") (if (>= ");
            sb.append(leftRight);
            sb.append(") ");
            sb.append(leftRight);
            sb.append(")))\n");

            return sb.toString();
        }

        // (assert (= (aplus x y) (mk-tuple (and (select x 1) (select y 1)) (max (select x 2) (select y 2)))))
        public Set<String> aplus(final String var, final String left, final String right) {

            final String lgeVar = this.yvFactory.createBoolVar();

            final StringBuilder sb = new StringBuilder("(assert (= ");
            sb.append(var);
            sb.append(" (mk-tuple (and ");
            sb.append(this.infinite(left));
            sb.append(" ");
            sb.append(this.infinite(right));
            sb.append(") (if ");
            sb.append(lgeVar);
            sb.append(" ");
            sb.append(this.value(left));
            sb.append(" ");
            sb.append(this.value(right));
            sb.append("))))\n");

            final Set<String> result = new LinkedHashSet<String>();
            result.add(sb.toString());
            result.add(this.age(lgeVar, left, right));
            return result;
        }

        // (assert (= (atimes x y) (mk-tuple (or (select x 1) (select y 1)) (+ (select x 2) (select y 2)))))
        public String atimes(final String var, final String left, final String right) {

            final StringBuilder sb = new StringBuilder("(assert (= ");
            sb.append(var);
            sb.append(" (mk-tuple (or ");
            sb.append(this.infinite(left));
            sb.append(" ");
            sb.append(this.infinite(right));
            sb.append(") (+ ");
            sb.append(this.value(left));
            sb.append(" ");
            sb.append(this.value(right));
            sb.append("))))\n");
            return sb.toString();
        }

        public String acompare(final String var, final String left, final String right, final ConstraintType ct) {

            switch (ct) {
            case GT:
                return this.agt(var, left, right);
            case GE:
                return this.age(var, left, right);
            case EQ:
                return this.aeq(var, left, right);
            default:
                throw new IllegalArgumentException("Unknown constraint type");
            }
        }
    }

    private static class YicesVarFactory {

        private static String PREFIX = "yi_";
        private int count = 0;
        private final List<String> arcticVars = new ArrayList<String>();
        private final List<String> boolVars = new ArrayList<String>();

        public String createArcticVar() {

            final String name = YicesVarFactory.PREFIX + String.valueOf(++this.count);
            this.arcticVars.add(name);
            return name;
        }

        public String createBoolVar() {

            final String name = YicesVarFactory.PREFIX + String.valueOf(++this.count);
            this.boolVars.add(name);
            return name;
        }

        public List<String> getArcticVars() {
            return this.arcticVars;
        }

        public List<String> getBoolVars() {
            return this.boolVars;
        }
    }
}
