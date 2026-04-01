package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Polynomial interpretation of terms over a certain signature.
 * Stolen from ../POLO/Interpretation.java and adapted to GPolys.
 * @param <C> The type of the coefficients.
 */
public class GInterpretation<C extends GPolyCoeff> {
    /**
     * A (semi)ring that operates on coefficients of type C.
     */
    protected final Semiring<C> ring;

    /**
     * A monoid that operates on monomials over variables.
     */
    protected final CMonoid<GMonomial<GPolyVar>> monoid;

    /**
     * An order that can put coefficients of type C in relation to 0.
     */
    protected final CoeffOrder<C> coeffOrder;

    /**
     * A flattening visitor to operate in inner polynomials.
     */
    protected final FlatteningVisitor<C, GPolyVar> fvInner;

    /**
     * A flattening visitor to operate on order polynomials.
     */
    protected final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter;

    /**
     * A (semi)ring used to operate on inner polynomials.
     */
    protected final Semiring<GPoly<C, GPolyVar>> polyRing;

    /**
     * The actual interpretation Pol(f) for function symbols f.
     */
    protected final Map<FunctionSymbol, OrderPoly<C>> pol;

    /**
     * This factory will be used to create constraints.
     */
    protected ConstraintFactory<C> constraintFactory;

    /**
     * This factory will be used to create OrderPolys.
     */
    protected final OrderPolyFactory<C> factory;

    /**
     * ranges for variables.
     */
    protected Map<GPolyVar, OPCRange<C>> ranges;

    /**
     * ax + by + c.
     */
    public static final int LINEAR = 1;

    /**
     * ax + by + cxy + d.
     */
    public static final int SIMPLE = -1;

    /**
     * f(x,y): ax + by + cxy + d, f(x): ax^2 + bx + c.
     */
    public static final int SIMPLE_MIXED = 0;

    /**
     * The prefix used for variables that are variables (all-quantified).
     */
    public static final String VARIABLE_PREFIX = "x_";
    /**
     * The prefix used for variables that are abstract coefficients.
     */
    public static final String COEFF_PREFIX = "ca_";

    /**
     * The prefix used for variables that will be used for usable rules.
     */
    public static final String ACTIVE_PREFIX = "ap_";

    /**
     * The papers explaining how this specific POLO works.
     */
    protected List<Citation> citations;

    /**
     * A counter for the used coefficients.
     */
    private int nextCoeff;

    /**
     * Creates an empty Interpretation.
     * @param factoryParam This factory will be used to create an
     * OrderPolyFactory which then will be used to create OrderPolys.
     * @param innerFactoryParam This factory will be used to create coefficients
     * for the OrderPolys.
     * @param constraintFactoryParam The constraint factory will be used to
     * create order poly constraints.
     * @param inner A FlatteningVisitor that is able to flatten the inner
     * inner polynomials.
     * @param outer A FlatteningVisitor that is able to flatten the outer
     * polynomials.
     * @param coeffOrderParam A CoeffOrder that is able to put some coefficient
     * of type C in relation to 0.
     * @param citationsParam The citations of the techniques used here
     * (e.g. POLO).
     */
    protected GInterpretation(final GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> factoryParam,
            final GPolyFactory<C, GPolyVar> innerFactoryParam, final ConstraintFactory<C> constraintFactoryParam,
            final FlatteningVisitor<C, GPolyVar> inner, final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> outer,
            final CoeffOrder<C> coeffOrderParam, final List<Citation> citationsParam) {
        this.factory = new OrderPolyFactory<>(factoryParam, innerFactoryParam);
        this.pol = new LinkedHashMap<>();
        this.ranges = new LinkedHashMap<>();
        this.citations = citationsParam;
        this.fvInner = inner;
        this.fvOuter = outer;
        this.monoid = outer.getMonoid();
        this.ring = inner.getRingC();
        this.polyRing = outer.getRingC();
        this.coeffOrder = coeffOrderParam;
        this.constraintFactory = constraintFactoryParam;
        this.nextCoeff = 1; // we rely on the first value for nextCoeff being 1!
    }

    /**
     * Creates an empty Interpretation.
     * @param factoryParam This factory will be used to create OrderPolys.
     * @param constraintFactoryParam The constraint factory will be used to
     * create order poly constraints.
     * @param inner A FlatteningVisitor that is able to flatten the inner
     * inner polynomials.
     * @param outer A FlatteningVisitor that is able to flatten the outer
     * polynomials.
     * @param coeffOrderParam A CoeffOrder that is able to put some coefficient
     * of type C in relation to 0.
     * @param citationsParam The citations of the techniques used here
     * (e.g. POLO).
     */
    private GInterpretation(final OrderPolyFactory<C> factoryParam, final ConstraintFactory<C> constraintFactoryParam,
            final FlatteningVisitor<C, GPolyVar> inner, final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> outer,
            final CoeffOrder<C> coeffOrderParam, final List<Citation> citationsParam) {
        this.factory = factoryParam;
        this.pol = new LinkedHashMap<>();
        this.ranges = new LinkedHashMap<>();
        this.nextCoeff = 1; // we rely on the first value for nextCoeff being 1!
        this.fvInner = inner;
        this.fvOuter = outer;
        this.citations = citationsParam;
        this.ring = inner.getRingC();
        this.polyRing = outer.getRingC();
        this.monoid = inner.getMonoid();
        this.coeffOrder = coeffOrderParam;
    }

    /**
     * Transform the set of term constraints to a set of order poly constraints.
     * @param constraints The term constraints.
     * @return A set of order poly constraints.
     */
    public Set<OrderPolyConstraint<C>> fromTermConstraints(final Collection<Constraint<TRSTerm>> constraints,
        final Abortion aborter) throws AbortionException {
        final Set<OrderPolyConstraint<C>> result = new LinkedHashSet<>(constraints.size());
        for (final Constraint<TRSTerm> constraint : constraints) {
            final TermPair tp = TermPair.create(constraint.x, constraint.y);
            final OrderPoly<C> left = this.interpretTerm(tp.getLhsInStandardRepresentation(), aborter);
            final OrderPoly<C> right = this.interpretTerm(tp.getRhsInStandardRepresentation(), aborter);
            final OrderPoly<C> minus = this.factory.minus(left, right);
            final ConstraintType ct = this.fromRelation(constraint.z);
            final OrderPolyConstraint<C> newConstraint = this.constraintFactory.createWithQuantifier(minus, ct);
            result.add(newConstraint);
        }
        return result;
    }

    /**
     * Transform the set of term constraints to a set of order poly constraints.
     * Also return the constant part of the resulting polynomial.
     * @param constraints The term constraints.
     * @return A set of order poly constraints.
     */
    public Map<OrderPolyConstraint<C>, GPoly<C, GPolyVar>> fromTermConstraintsWithConstants(final Collection<Constraint<TRSTerm>> constraints,
        final Abortion aborter) throws AbortionException {
        final Map<OrderPolyConstraint<C>, GPoly<C, GPolyVar>> result = new LinkedHashMap<>(constraints.size());
        for (final Constraint<TRSTerm> constraint : constraints) {
            final TermPair tp = TermPair.create(constraint.x, constraint.y);
            final OrderPoly<C> left = this.interpretTerm(tp.getLhsInStandardRepresentation(), aborter);
            final OrderPoly<C> right = this.interpretTerm(tp.getRhsInStandardRepresentation(), aborter);
            final OrderPoly<C> minus = this.factory.minus(left, right);
            final ConstraintType ct = this.fromRelation(constraint.z);
            final OrderPolyConstraint<C> newConstraint = this.constraintFactory.createWithQuantifier(minus, ct);
            this.fvOuter.applyTo(minus);
            final GPoly<C, GPolyVar> constant = minus.getConstantPart(this.polyRing, this.monoid);
            result.put(newConstraint, constant);
        }
        return result;
    }

    /**
     * @return the ranges.
     */
    public Map<GPolyVar, OPCRange<C>> getRanges() {
        return this.ranges;
    }

    /**
     * Transform the set of term constraints to a set of order poly constraints.
     * For every term constraint a variable is given which is subtracted from
     * the resulting OrderPolyConstraint.
     * @param constraints The term constraints with a variable that should be
     * subtracted.
     * @return A set of order poly constraints.
     */
    public Set<OrderPolyConstraint<C>> fromTermConstraints(final Map<Constraint<TRSTerm>, GPolyVar> constraints,
        final Abortion aborter) throws AbortionException {
        final Set<OrderPolyConstraint<C>> result = new LinkedHashSet<>(constraints.size());
        for (final Map.Entry<Constraint<TRSTerm>, GPolyVar> entry : constraints.entrySet()) {
            aborter.checkAbortion();
            final Constraint<TRSTerm> constraint = entry.getKey();
            final TermPair tp = TermPair.create(constraint.x, constraint.y);
            final OrderPoly<C> left = this.interpretTerm(tp.getLhsInStandardRepresentation(), aborter);
            final OrderPoly<C> right = this.interpretTerm(tp.getRhsInStandardRepresentation(), aborter);
            aborter.checkAbortion();
            OrderPoly<C> minus = this.factory.minus(left, right);
            final OrderPoly<C> polyFromVariable = this.factory.buildFromInnerVariable(entry.getValue());
            minus = this.factory.minus(minus, polyFromVariable);
            final ConstraintType ct = this.fromRelation(constraint.z);
            final OrderPolyConstraint<C> newConstraint = this.constraintFactory.createWithQuantifier(minus, ct);
            result.add(newConstraint);
        }
        return result;
    }

    /**
     * Convert the given relation to a constraint type.
     * @param rel The relation.
     * @return The corresponding constraint type.
     */
    private ConstraintType fromRelation(final OrderRelation rel) {
        if (rel.equals(OrderRelation.EQ)) {
            return ConstraintType.EQ;
        } else if (rel.equals(OrderRelation.GE)) {
            return ConstraintType.GE;
        } else if (rel.equals(OrderRelation.GR)) {
            return ConstraintType.GT;
        } else {
            assert (false);
            return null;
        }
    }

    /**
     * @return the factory used to create OrderPolys.
     */
    public OrderPolyFactory<C> getFactory() {
        return this.factory;
    }

    /**
     * @return a copy of the polynomial interpretation encapsulated by this
     *  Interpretation
     */
    public Map<FunctionSymbol, OrderPoly<C>> getPol() {
        return new LinkedHashMap<>(this.pol);
    }

    /**
     * @return a new coefficient variable.
     */
    public final GPolyVar getNextCoeff(final OPCRange<C> range) {
        return this.getNextCoeff(GInterpretation.COEFF_PREFIX, range);
    }

    /**
     * @return a new coefficient variable.
     */
    public final GPolyVar getNextCoeff(final String prefix, final OPCRange<C> range) {
        final GPolyVar var = GAtomicVar.createVariable(prefix + (this.nextCoeff++));
        if (range != null) {
            this.ranges.put(var, range);
        }
        return var;
    }

    /**
     * @return a new logical variable.
     */
    protected final OPCLogVar<C> getNextLogVar(final String prefix) {
        return this.constraintFactory.createLogVar(prefix + (this.nextCoeff++));
    }

    /**
     * @return a new OrderPoly representing a fresh constant.
     */
    public OrderPoly<C> getNextCoeffOrderPoly(final FunctionSymbol fs) {
        return this.factory.buildFromCoeff(this.getNextCoeffPoly(fs));
    }

    /**
     * @return a new inner GPoly representing a fresh coeff.
     */
    protected GPoly<C, GPolyVar> getNextCoeffPoly(final FunctionSymbol fs) {
        return this.factory.getInnerFactory().buildFromVariable(this.getNextCoeff(null));
    }

    /**
     * Creates a generic (with indefinite coeffs a_i) interpretation of
     * degree <code>degree</code> for the term constraints
     * <code>constraints</code>.
     *
     * @param <C> The type of the coefficients.
     * @param constraints we want an interpretation where all occurring
     * function symbols of constraints are mapped to a polynomial.
     * @param form The form of the generic polynomial interpretation
     * @param factory This factory will be used to create new OrderPolys.
     * @param innerFactory This factory will be used to create coefficients for
     * the OrderPolys.
     * @param constraintFactory This factory will be used to create constraints.
     * @param inner A FlatteningVisitor that is able to flatten the inner
     * inner polynomials.
     * @param outer A FlatteningVisitor that is able to flatten the outer
     * polynomials.
     * @param coeffOrderParam A CoeffOrder that is able to put some coefficient
     * of type C in relation to 0.
     * @param citationsParam The list of citations of the techniques used here
     * (e.g. POLO).
     * @return the resulting generic interpretation for constraints.
     */
    public static <C extends GPolyCoeff> GInterpretation<C> create(final Iterable<Constraint<TRSTerm>> constraints,
        final GInterpretationMode<C> form,
        final GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> factory,
        final GPolyFactory<C, GPolyVar> innerFactory,
        final ConstraintFactory<C> constraintFactory,
        final FlatteningVisitor<C, GPolyVar> inner,
        final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> outer,
        final CoeffOrder<C> coeffOrderParam,
        final List<Citation> citationsParam,
        final Abortion aborter) throws AbortionException {
        final GInterpretation<C> interpretation =
            new GInterpretation<>(factory, innerFactory, constraintFactory, inner, outer, coeffOrderParam,
                citationsParam);
        for (final Constraint<TRSTerm> constraint : constraints) {
            interpretation.extend(constraint, form, aborter);
        }

        return interpretation;
    }

    /**
     * @param factory The GPolyFactory that will be used to create new
     * OrderPolys.
     * @param innerFactory This factory will be used to create coefficients for
     * the OrderPolys.
     * @param constraintFactory This factory will be used to create constraints.
     * @param <C> The type of the coefficients.
     * @param inner A FlatteningVisitor that is able to flatten the inner
     * inner polynomials.
     * @param outer A FlatteningVisitor that is able to flatten the outer
     * polynomials.
     * @param coeffOrderParam A CoeffOrder that is able to put some coefficient
     * of type C in relation to 0.
     * @param citationsParam The citations of the techniques used here
     * (e.g. POLO).
     * @return an empty interpretation.
     */
    public static <C extends GPolyCoeff> GInterpretation<C> create(final GPolyFactory<GPoly<C, GPolyVar>, GPolyVar> factory,
        final GPolyFactory<C, GPolyVar> innerFactory,
        final ConstraintFactory<C> constraintFactory,
        final FlatteningVisitor<C, GPolyVar> inner,
        final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> outer,
        final CoeffOrder<C> coeffOrderParam,
        final List<Citation> citationsParam) {
        return new GInterpretation<>(factory, innerFactory, constraintFactory, inner, outer, coeffOrderParam,
            citationsParam);
    }

    /**
     * For each function symbol f with some interpretation pol the constraint
     * (Q pol) > 0 will be created. Here Q is a quantifier
     * "exists a,b,c forall x,y,z".
     *
     * @return poly constraints which ensure strong monotonicity of this.
     */
    public Set<OrderPolyConstraint<C>> getStrongMonotonicityConstraints() {
        final SpecializedGInterpretation specGInt = this.ring.getSpecializedGInterpretation();
        return specGInt.getStrongMonotonicityConstraints(this);
    }

    /**
     * Extends this for the new function symbols of the term constraint
     * constraint.
     *
     * @param constraint this is to be extended for constraint
     * @param form the form of the desired interpretation
     */
    public void extend(final Constraint<TRSTerm> constraint, final GInterpretationMode<C> form, final Abortion aborter)
            throws AbortionException {
        for (final FunctionSymbol fSym : constraint.getLeft().getFunctionSymbols()) {
            this.extend(fSym, form, aborter);
        }
        for (final FunctionSymbol fSym : constraint.getRight().getFunctionSymbols()) {
            this.extend(fSym, form, aborter);
        }
    }

    /**
     * Extends this for all symbols that do not already have
     * an interpretation in this.
     *
     * @param symbols the function symbols for which we want an interpretation.
     * @param form the form of the desired interpretation
     */
    public void extend(final Iterable<? extends HasFunctionSymbols> iterable,
        final GInterpretationMode<C> form,
        final Abortion aborter) throws AbortionException {
        for (final HasFunctionSymbols hfs : iterable) {
            for (final FunctionSymbol symbol : hfs.getFunctionSymbols()) {
                this.extend(symbol, form, aborter);
            }
        }
    }

    /**
     * Extends this for symbol if symbol does not already have
     * an interpretation in this.
     *
     * @param symbol the function symbol for which we want an interpretation.
     * @param form the form of the desired interpretation
     */
    public void extend(final FunctionSymbol symbol, final GInterpretationMode<C> form, final Abortion aborter)
            throws AbortionException {
        if (!this.pol.containsKey(symbol)) {
            this.pol.put(symbol, this.getPolynomialFromFunction(symbol, form, aborter));
        }
    }

    /**
    * Maps symbol to polynomial in this if symbol does not already have
    * an interpretation in this.
    *
    * @param symbol the function symbol which we want to interpret
    *  as polynomial
    * @param polynomial the proposed polynomial interpretation for symbol
    */
    public void extend(final FunctionSymbol symbol, final OrderPoly<C> polynomial, final Abortion aborter)
            throws AbortionException {
        aborter.checkAbortion();
        if (this.pol.containsKey(symbol)) {
            return;
        }
        this.pol.put(symbol, polynomial);
    }

    /**
     * @return the maximum degree of some polynomial contained by this (where
     *         e.g. x^2*y^3 has degree 2+3 = 5)
     */
    public BigInteger getDegree() {
        BigInteger res = BigInteger.ZERO;
        for (final Entry<FunctionSymbol, OrderPoly<C>> e : this.pol.entrySet()) {
            final OrderPoly<C> oPoly = new OrderPoly<>(this.fvOuter.applyTo(e.getValue()));
            final BigInteger degree = oPoly.getDegree();
            if (degree.compareTo(res) > 0) {
                res = degree;
            }
        }
        return res;
    }

    /**
     * Calculates the polynomial interpretation of a term constraint based on
     * the present interpretation of the signature.
     *
     * @param constraint
     *            the term constraint to convert
     * @return the polynomial interpretation of the given term constraint
     */
    public OrderPolyConstraint<C> getPolynomialConstraint(final Constraint<TRSTerm> constraint, final Abortion aborter)
            throws AbortionException {
        final TermPair tp = TermPair.create(constraint.x, constraint.y);
        final OrderPoly<C> left = this.interpretTerm(tp.getLhsInStandardRepresentation(), aborter);
        final OrderPoly<C> right = this.interpretTerm(tp.getRhsInStandardRepresentation(), aborter);
        final OrderPoly<C> polynomial = this.factory.minus(left, right);

        ConstraintType type;
        switch (constraint.getType()) {
        case EQ:
            type = ConstraintType.EQ;
            break;
        case GE:
            type = ConstraintType.GE;
            break;
        case GR:
            type = ConstraintType.GT;
            break;
        default:
            throw new RuntimeException("Can't make a orderpolyconstraint type out of " + constraint.getType() + "!");
        }
        return this.constraintFactory.createWithQuantifier(polynomial, type);
    }

    /**
     * Calculates the polynomial interpretation of a rule based on the
     * present interpretation of the signature.
     *
     * @param rule to be converted to a VarPolyConstraint
     * @param type type of the resulting constraint (GT/GE/EQ)
     * @return a OrderPolyConstraint which encodes the polynomial
     *  interpretation of rule of type type.
     */
    public OrderPolyConstraint<C> getPolynomialConstraint(final Rule rule,
        final ConstraintType type,
        final Abortion aborter) throws AbortionException {
        final OrderPoly<C> left = this.interpretTerm(rule.getLhsInStandardRepresentation(), aborter);
        aborter.checkAbortion();
        final OrderPoly<C> right = this.interpretTerm(rule.getRhsInStandardRepresentation(), aborter);
        aborter.checkAbortion();
        final OrderPoly<C> poly = this.factory.minus(left, right);
        return this.constraintFactory.createWithQuantifier(poly, type);
    }

    /**
     * Performs the actual generation of a generic polynomial interpretation
     * for the FunctionSymbol symbol.
     *
     * @param symbol we want its generic polynomial interpretation
     * @param form the form of the desired interpretation
     * @return the resulting polynomial interpretation
     */
    public OrderPoly<C> getPolynomialFromFunction(final FunctionSymbol symbol,
        final GInterpretationMode<C> form,
        final Abortion aborter) throws AbortionException {
        final List<OrderPoly<C>> variables = this.getVariablesForFunction(symbol);
        aborter.checkAbortion();
        return form.getPolynomial(this, symbol, variables);
    }

    /**
     * Returns a list of variables to build an interpretation for a function
     * symbol by hand (i.e. via <code>extend(FunctionSymbol, OrderPoly)</code>).
     */
    public List<OrderPoly<C>> getVariablesForFunction(final FunctionSymbol symbol) {
        final int arity = symbol.getArity();
        final ArrayList<OrderPoly<C>> variables = new ArrayList<>(arity);
        for (int i = 0; i < arity; ++i) {
            final GPolyVar var = this.getVariableForFunctionSymbolArgument(i);
            variables.add(i, this.factory.buildFromVariable(var));
        }
        return variables;
    }

    /**
     * Returns a variable for the i-th argument of a function symbol (counting
     * from 0!).
     */
    public GPolyVar getVariableForFunctionSymbolArgument(final int argument) {
        return GAtomicVar.createVariable(GInterpretation.VARIABLE_PREFIX + (argument + 1));
    }

    /**
     * Interprets a term t with a GPoly, built up using
     * the polynomial interpretations of its function symbols.
     *
     * @param t the term to be interpreted
     * @return the polynomial which corresponds to t in this
     */
    public OrderPoly<C> interpretTerm(final TRSTerm t, final Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert ((t instanceof TRSFunctionApplication) || (t instanceof TRSVariable));
            // if other terms should ever be created, the below code
            // needs to be checked
        }

        OrderPoly<C> result;

        if (t.isVariable()) {
            // easy: Variable
            result =
                this.factory.concat(this.factory.getCoeffOne(),
                    this.factory.buildVariable(GAtomicVar.createVariable(t.getName())));
        } else {
            // FunctionApplication
            final TRSFunctionApplication fApp = (TRSFunctionApplication) t;

            // First get the interpretation of the root symbol
            result = this.pol.get(fApp.getRootSymbol());

            if (result.containsVariable()) {
                final Collection<GPolyVar> vars = result.getVariables();
                // we need to interpret at least one argument
                final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
                Map<GPolyVar, GPoly<GPoly<C, GPolyVar>, GPolyVar>> substitution;
                // x_j |-> poly interpretation of t|_j

                final int size = args.size();
                substitution = new LinkedHashMap<>(size);
                for (int i = 0; i < size; ++i) {
                    aborter.checkAbortion();
                    final GPolyVar argVar = this.getVariableForFunctionSymbolArgument(i);

                    if (vars.contains(argVar)) {
                        final OrderPoly<C> argPoly = this.interpretTerm(args.get(i), aborter);
                        substitution.put(argVar, argPoly.unwrap());
                    }
                }

                /*
                 * Replace the variables in the interpretation of the root symbol by the interpretations of the
                 * arguments.
                 */
                result = this.factory.substituteVariables(result, substitution, this.polyRing, aborter);
            }
        }
        // System.out.println("InterpretTerm: [" + t + "] = " + factory.wrap(result).exportFlatDeep(fvInner, fvOuter, new PLAIN_Util()));
        return result;
    }

    /**
     *
     * @return whether this interprets any FunctionSymbol
     */
    public boolean isEmpty() {
        return this.pol.isEmpty();
    }

    /**
     * @param f we want its interpretation
     * @return the interpretation of f in this
     */
    public OrderPoly<C> get(final FunctionSymbol f) {
        return this.pol.get(f);
    }

    /**
     * Allows to interpret a FunctionSymbol by some polynomial supplied by
     * the caller. The FunctionSymbol must not have been interpreted by this
     * so far.
     *
     * @param f - FunctionSymbol that has not been interpreted by this so far
     * @param p - Interpretation for f, must not be null, all its factors must
     *  be positive, its variables must a subset of
     *  {VARIABLE_PREFIX + "1", ..., VARIABLE_PREFIX + "n"} if f has arity n
     *  (VARIABLE_PREFIX + "i" stands for the i-th argument of f)
     */
    public void put(final FunctionSymbol f, final OrderPoly<C> p) {
        if (Globals.useAssertions) {
            assert (!this.pol.containsKey(f));
            assert f != null;
            assert p != null;
            final Set<GPolyVar> allowedVars = new LinkedHashSet<>(f.getArity());
            final int n = f.getArity();
            for (int i = 1; i <= n; ++i) {
                allowedVars.add(this.getVariableForFunctionSymbolArgument(i));
            }
            assert allowedVars.containsAll(p.getVariables());
        }
        this.pol.put(f, p);
    }

    /**
     * Calculates a new Interpretation as the specialization of the current one
     * and sets all coefficient variables to value in given state. Those
     * coefficient variables that do not occur in the state will be set to
     * defValue.
     *
     * @param state maps indefinite coefficient variables to coefficients by
     * which they are supposed to be substituted.
     * @param defValue the value for all those coefficient variables which do
     * not occur.
     * @return a GInterpretation specialized according to the given map and
     * default value.
     */
    public GInterpretation<C> specialize(final Map<GPolyVar, C> state, final C defValue, final Abortion aborter)
            throws AbortionException {
        final GInterpretation<C> specialization =
            new GInterpretation<>(this.factory, this.constraintFactory, this.fvInner, this.fvOuter, this.coeffOrder,
                this.citations);
        this.applySpecialization(specialization, state, defValue, aborter);
        return specialization;
    }

    protected void applySpecialization(final GInterpretation<C> specialization,
        final Map<GPolyVar, C> state,
        final C defValue,
        final Abortion aborter) throws AbortionException {
        // no complete specialization
        specialization.pol.putAll(this.pol);
        for (final Entry<FunctionSymbol, OrderPoly<C>> entry : this.pol.entrySet()) {
            aborter.checkAbortion();
            OrderPoly<C> polynomial = entry.getValue();

            // replace according to state
            final Map<GPolyVar, C> newState = new LinkedHashMap<>(state);

            // replace every other variable by defValue
            for (final GPolyVar var : polynomial.getInnerVariables()) {
                if (!newState.containsKey(var)) {
                    newState.put(var, defValue);
                }
            }

            polynomial = this.deepSubstitute(polynomial, newState, aborter);
            specialization.pol.put(entry.getKey(), polynomial);
            specialization.nextCoeff = this.nextCoeff;
        }
        aborter.checkAbortion();
    }

    /**
     * Substitute the coefficient variables according to the given map.
     * @param polynomial The polynomial which contains the coefficients.
     * @param state The map defining the substutution.
     * @return A OrderPoly where the variables inside the coefficients are
     * changed according to state.
     */
    protected OrderPoly<C> deepSubstitute(final OrderPoly<C> polynomial,
        final Map<GPolyVar, C> state,
        final Abortion aborter) throws AbortionException {
        final Map<GPolyVar, GPoly<C, GPolyVar>> subst = new LinkedHashMap<>(state.size());
        final VarPartNode<GPolyVar> varOne = this.factory.getVarOne();

        // provide a map that can be used for substitutions over GPOLYs.
        for (final Map.Entry<GPolyVar, C> entry : state.entrySet()) {
            final GPolyVar var = entry.getKey();
            final C coeff = entry.getValue();
            if (this.ring.zero().equals(coeff)) {
                subst.put(var, this.factory.getInnerFactory().zero());
            } else if (this.ring.one().equals(coeff)) {
                subst.put(var, this.factory.getInnerFactory().one());
            } else {
                final GPoly<C, GPolyVar> substPoly = this.factory.getInnerFactory().concat(coeff, varOne);
                subst.put(var, substPoly);
            }
        }

        final Map<GPoly<C, GPolyVar>, GPoly<C, GPolyVar>> coeffMap = new LinkedHashMap<>();
        // substitute in each coefficient
        final Set<GPoly<C, GPolyVar>> allCoeffs = new LinkedHashSet<>(polynomial.getCoeffs());
        for (final GPoly<C, GPolyVar> coeff : allCoeffs) {
            if (coeff != null) {
                GPoly<C, GPolyVar> result = coeff;
                result = this.factory.getInnerFactory().substituteVariables(result, subst, this.ring, aborter);

                // take care that the new coeff will be used in the final result
                if (!coeff.equals(result)) {
                    coeffMap.put(coeff, result);
                }
            }
        }

        /*
         * If we replace every old coefficient by the new values, with the substitution a/0 we may have turned ax+1 to
         * 0x+1. To clean the resulting polynomial, we replace the known values for 0 and 1 by the default polynomials
         * for these values, so that optimizations can take place.
         */
        coeffMap.put(this.factory.getInnerFactory().buildFromCoeff(this.ring.zero()),
            this.factory.getInnerFactory().zero());
        coeffMap.put(this.factory.getInnerFactory().buildFromCoeff(this.ring.one()),
            this.factory.getInnerFactory().one());

        // build a new (outer) polynomial with the new coefficients
        OrderPoly<C> result = polynomial;
        for (final Map.Entry<GPoly<C, GPolyVar>, GPoly<C, GPolyVar>> entry : coeffMap.entrySet()) {
            result = this.factory.substituteCoefficient(result, entry.getKey(), entry.getValue(), this.polyRing);
        }
        return result;
    }

    /**
     * Exports the mapping from function symbols to polynomials with variables.
     *
     * @param eu the export util
     * @return the exported version of the interpretation
     */
    public String export(final Export_Util eu) {
        final StringBuilder result = new StringBuilder(this.getDescription(eu) + eu.cite(this.citations) + ":\n");

        final int size = this.pol.size();
        final List<String> rows = new ArrayList<>(size);

        Map<FunctionSymbol, OrderPoly<C>> sortedPol; // for ordered display
        sortedPol = new TreeMap<>(this.pol);
        for (final Map.Entry<FunctionSymbol, OrderPoly<C>> entry : sortedPol.entrySet()) {
            String row = this.exportPoly(eu, entry.getKey(), entry.getValue(), null, null, null);
            // nasty hack for equidistant lines in HTML (and hence the GUI)
            if (eu instanceof HTML_Util) {
                row += "<sup>&nbsp;</sup> <sub>&nbsp;</sub>";
            }
            rows.add(row);
        }

        result.append(eu.set(rows, Export_Util.RULES));
        return result.toString();
    }

    protected String exportPoly(final Export_Util eu,
        final FunctionSymbol functionSymbol,
        final OrderPoly<C> polynomial,
        final RelDependency relDependency,
        final List<ImmutablePair<FunctionSymbol, Integer>> context,
        final List<? extends TRSTerm> args) {
        final StringBuilder line = new StringBuilder("POL(");

        final int arity = functionSymbol.getArity();

        final StringBuilder functionWithVars = new StringBuilder(functionSymbol.export(eu));
        if (arity > 0) {
            functionWithVars.append("(");
            for (int i = 1; i <= arity; ++i) {
                if (args == null || args.get(i - 1) == null) {
                    StringBuilder varBuf;
                    final String var = GInterpretation.VARIABLE_PREFIX + i;
                    final String[] split = var.split("_", 2);
                    varBuf = new StringBuilder(split[0]);
                    if (split.length > 1) {
                        varBuf.append(eu.sub(split[1]));
                    }
                    functionWithVars.append(varBuf);
                } else {
                    functionWithVars.append(args.get(i - 1).export(eu));
                }
                if (i < arity) {
                    functionWithVars.append(", ");
                }
            }
            functionWithVars.append(")");
        }

        line.append(eu.bold(functionWithVars.toString()));
        if (relDependency != null) {
            line.append(eu.sup(relDependency.getK().toString()));
        }
        if (context != null) {
            line.append(" @ ");
            final Set<String> contextStrings = new LinkedHashSet<>();
            for (final ImmutablePair<FunctionSymbol, Integer> contextEntry : context) {
                contextStrings.add(contextEntry.x + "/" + contextEntry.y);
            }
            line.append(eu.set(contextStrings, Export_Util.NICE_SIMPLE));
        }
        line.append(") = ");
        final MaxMinToVarVisitor<C> maxMinToVarVisitor =
            new MaxMinToVarVisitor<>(this.fvInner, this.fvOuter, this.factory.getFactory());
        final GPoly<GPoly<C, GPolyVar>, GPolyVar> poly = maxMinToVarVisitor.applyTo(polynomial);
        if (!poly.isFlat(this.getOuterRingMonoid())) {
            this.fvOuter.applyTo(poly);
        }
        // get the string representation of the polynomial where all
        // values are flattened
        line.append(this.factory.wrap(poly).exportFlatDeep(this.fvInner, this.fvOuter, eu));

        return line.toString();
    }

    protected String getDescription(final Export_Util eu) {
        return "Polynomial interpretation ";
    }

    /**
     * @return a simple string representation.
     */
    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * Create the constraints defining the active-ness of rules and create the
     * constraints for the rules based on that.
     * @param usableRules The rules with the corresponding active condition.
     * @param form The form of the polynomials.
     * @param boolRange The standard range for boolean variables (over C!).
     * @param aborter some aborter.
     * @return A constraint which includes all constraints for the active
     * conditions and the constraints for the usable rules.
     * @throws AbortionException when the aborter kicks in.
     */
    public OrderPolyConstraint<C> getActiveRuleConstraints(final Map<? extends GeneralizedRule, QActiveCondition> usableRules,
        final GInterpretationMode<C> form,
        final OPCRange<C> boolRange,
        final Abortion aborter) throws AbortionException {
        // build active usable rules constraints
        final Set<OrderPolyConstraint<C>> activeConstraints = new LinkedHashSet<>();
        final Set<OrderPolyConstraint<C>> ruleConstraints = new LinkedHashSet<>();

        final Map<QActiveCondition, GPolyVar> activeConditions = new LinkedHashMap<>();

        // extend signature
        for (final GeneralizedRule rule : usableRules.keySet()) {
            for (final FunctionSymbol f : rule.getFunctionSymbols()) {
                this.extend(f, form, aborter);
            }
        }

        // build constraints for activation conditions and rules
        for (final Map.Entry<? extends GeneralizedRule, QActiveCondition> usable : usableRules.entrySet()) {
            final QActiveCondition qac = usable.getValue();
            final boolean isTrue = (qac == QActiveCondition.TRUE);
            GPoly<C, GPolyVar> activeConditionPoly;
            if (isTrue) {
                activeConditionPoly = null;
            } else {
                // Return a variable that, when set to 1, denotes the rule is
                // usable. The function getActiveCondition also creates the
                // constraints that are needed to decide how to set the value
                // of that variable.
                activeConditionPoly =
                    this.getActiveCondition(qac, activeConstraints, activeConditions, boolRange, aborter);
            }

            final GeneralizedRule rule = usable.getKey();
            final TRSTerm left = rule.getLhsInStandardRepresentation();
            final TRSTerm right = rule.getRhsInStandardRepresentation();

            // build rule constraint
            OrderPoly<C> constraint = this.factory.minus(this.interpretTerm(left, aborter), this.interpretTerm(right, aborter));
            aborter.checkAbortion();

            // multiply it with active condition
            final OrderPoly<C> acOrderPoly = this.factory.buildFromCoeff(activeConditionPoly);
            if (!isTrue) {
                constraint = this.factory.times(constraint, acOrderPoly);
            }
            final OrderPolyConstraint<C> ruleConstraint =
                this.constraintFactory.createWithQuantifier(constraint, ConstraintType.GE);
            ruleConstraints.add(ruleConstraint);
        }

        // build constraints for activation conditions and equations
        final Set<OrderPolyConstraint<C>> constraints = new LinkedHashSet<>(ruleConstraints);
        constraints.addAll(activeConstraints);
        final OrderPolyConstraint<C> result = this.constraintFactory.createAnd(constraints);
        return result;
    }

    /**
     * Create a variable for the given QActiveConstraint and ensure (by adding
     * constraints) that the value chosen for this variable reflects if the
     * rule is usable or not.
     * @param qac The QActiveCondition.
     * @param activeConstraints The set where additional constraints will be
     * added.
     * @param cache A cache for already handled QActiveConditions.
     * @param boolRange the range for new (pseudo) boolean variables.
     * @param aborter Some aborter.
     * @return A variable that may only be set to 0 if the rule is not usable.
     * @throws AbortionException when the aborter kicks in.
     */
    public GPoly<C, GPolyVar> getActiveCondition(final QActiveCondition qac,
        final Set<OrderPolyConstraint<C>> activeConstraints,
        final Map<QActiveCondition, GPolyVar> cache,
        final OPCRange<C> boolRange,
        final Abortion aborter) throws AbortionException {
        GPolyVar activeCondition = cache.get(qac);
        GPoly<C, GPolyVar> activeConditionPoly;
        // do we already have an active Condition or do we need to create a
        // new one?
        if (activeCondition == null) {
            // we need a new one

            // get fresh variable for active condition
            final String name = GInterpretation.ACTIVE_PREFIX + (this.nextCoeff++);
            activeCondition = GAtomicVar.createVariable(name);
            this.ranges.put(activeCondition, boolRange);
            cache.put(qac, activeCondition);
            activeConditionPoly = this.factory.getInnerFactory().buildFromVariable(activeCondition);

            // if we have f/1^g/2 v h/3 then build
            // "(activeCondition - 1) * f/1 * g/2 = 0" and
            // "(activeCondition - 1) * h/3 = 0"
            this.addActiveConstraints(activeConstraints, qac, activeConditionPoly, aborter);
        } else {
            activeConditionPoly = this.factory.getInnerFactory().buildFromVariable(activeCondition);
        }
        return activeConditionPoly;
    }

    /**
     * Adds for a given active condition and the corresponding coefficient
     * "activeCondition" those constraints to the "constraints" set such that
     * the activeCondition = 1 is enforced if the activation condition evaluates
     * to true.
     * @param constraints we add the new constraints to this set
     * @param condition this is the qactive condition
     * @param acCoeff the coefficient which should store "condition is active"
     * @param aborter Some aborter.
     * @throws AbortionException when the aborter kicks in.
     */
    public void addActiveConstraints(final Set<OrderPolyConstraint<C>> constraints,
        final QActiveCondition condition,
        final GPoly<C, GPolyVar> acCoeff,
        final Abortion aborter) throws AbortionException {
        // ac is (b - 1)
        final GPoly<C, GPolyVar> ac =
            this.factory.getInnerFactory().minus(acCoeff, this.factory.getInnerFactory().one());

        nextAndConditions: for (final Set<Pair<FunctionSymbol, Integer>> andCondition : condition.getSetRepresentation()) {
            if (aborter != null) {
                aborter.checkAbortion();
            }
            GPoly<C, GPolyVar> product = this.factory.getInnerFactory().one();
            for (final Pair<FunctionSymbol, Integer> pair : andCondition) {
                final OrderPoly<C> poly = this.pol.get(pair.x);
                final int position = pair.y.intValue();
                final GPolyVar var = this.getVariableForFunctionSymbolArgument(position);
                this.fvOuter.applyTo(poly);

                // get all the coefficients for the current position
                final List<GPoly<C, GPolyVar>> coeffPolys = poly.getCoeffsFromMap(var, this.polyRing, this.monoid);

                // sum up the coefficients
                final GPoly<C, GPolyVar> coeffPoly = this.factory.getInnerFactory().plus(coeffPolys);
                this.fvInner.applyTo(coeffPoly);
                final C constantPart = coeffPoly.getConstantPart(this.ring, this.monoid);
                if (this.coeffOrder.signum(constantPart) != 0) {
                    // no matter how the inner variables will be set, this
                    // position is always active (caused by the constant part)
                    continue;
                } else {
                    if (coeffPoly.equals(this.ring.zero())) {
                        // the whole polynomial is zero, so the position is
                        // never active
                        continue nextAndConditions;
                    }
                    // it is not clear if the position is active, so build
                    // some constraint out of the coefficients.
                    product = this.factory.getInnerFactory().times(product, coeffPoly);
                }
            }

            final OrderPoly<C> acCoeffOrderPoly = this.factory.buildFromCoeff(ac);
            this.fvInner.applyTo(product);
            if (this.coeffOrder.signum(product.getConstantPart(this.ring, this.monoid)) != 0) {
                // the constant part is not 0, so the position is active
                constraints.add(this.constraintFactory.createWithQuantifier(acCoeffOrderPoly, ConstraintType.EQ));
                return;
            } else {
                // the absolute coefficient value is not known, so build
                // a constraint defining the active-ness.
                final OrderPoly<C> poly =
                    this.factory.buildFromCoeff(this.factory.getInnerFactory().times(ac, product));
                constraints.add(this.constraintFactory.createWithQuantifier(poly, ConstraintType.EQ));
            }
        }
    }

    /**
     * Determine if the given constraint is fulfilled.
     * This method must be called after specialization.
     * @param condition A QActiveCondition.
     * @return true iff the QActiveCondition is fulfilled.
     */
    public boolean solvesQActiveConstraint(final QActiveCondition condition) {
        nextAndConditions: for (final Set<Pair<FunctionSymbol, Integer>> andCondition : condition.getSetRepresentation()) {
            for (final Pair<FunctionSymbol, Integer> pair : andCondition) {
                final FunctionSymbol f = pair.x;
                final OrderPoly<C> polF = this.pol.get(f);
                this.fvOuter.applyTo(polF);
                final int position = pair.y.intValue();
                final GPolyVar var = this.getVariableForFunctionSymbolArgument(position);
                final GPoly<C, GPolyVar> coeffPoly =
                    this.factory.getInnerFactory().plus(polF.getCoeffsFromMap(var, this.polyRing, this.monoid));
                this.fvInner.applyTo(coeffPoly);
                if (Globals.useAssertions) {
                    assert (coeffPoly.isFlat(this.ring, this.monoid) && coeffPoly.isConstant());
                }
                final C constantPart = coeffPoly.getConstantPart(this.ring, this.monoid);
                if (this.coeffOrder.signum(constantPart) != 0) {
                    // the constant part is not 0, so this position is active
                    continue;
                } else {
                    continue nextAndConditions;
                }
            }
            return true;
        }
        return false;
    }

    /**
     * @param f - a function symbol that must be in the underlying signature;
     *  non-null
     * @param i - an argument position of f (in {0, ..., f.getArity()-1})
     * @return whether f is guaranteed to be monotonic in its i-th argument
     *  (false negatives may occur)
     */
    public boolean isMonotonicIn(final FunctionSymbol f, final int i) {
        final OrderPoly<C> fPol = this.pol.get(f);
        final GPolyVar var = this.getVariableForFunctionSymbolArgument(i);
        return this.ring.getSpecializedGInterpretation().isStronglyMonotonic(this, fPol, var);
    }

    public ConstraintFactory<C> getConstraintFactory() {
        return this.constraintFactory;
    }

    public FlatteningVisitor<C, GPolyVar> getFvInner() {
        return this.fvInner;
    }

    public FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> getFvOuter() {
        return this.fvOuter;
    }

    public Semiring<GPoly<C, GPolyVar>> getPolyRing() {
        return this.polyRing;
    }

    public Semiring<C> getRing() {
        return this.ring;
    }

    public CMonoid<GMonomial<GPolyVar>> getMonoid() {
        return this.monoid;
    }

    /**
     * The Pair containing the semiring and the monoid
     */
    public Pair<Semiring<C>, CMonoid<GMonomial<GPolyVar>>> getInnerRingMonoid() {
        return new Pair<>(this.ring, this.monoid);
    }

    /**
     * The Pair containing the ring and the monoid
     */
    public final Pair<Semiring<GPoly<C, GPolyVar>>, CMonoid<GMonomial<GPolyVar>>> getOuterRingMonoid() {
        return new Pair<>(this.polyRing, this.monoid);
    }

    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData, final Element domain) {
        final Element type =
            CPFTag.TYPE.create(
                doc,
                CPFTag.POLYNOMIAL.create(
                    doc,
                    CPFTag.DOMAIN.create(doc, domain),
                    CPFTag.DEGREE.create(doc, this.getDegree().toString())));
        final Element i = CPFTag.INTERPRETATION.create(doc, type);
        final Semiring<C> innerRing = this.fvInner.getRingC();
        for (final Map.Entry<FunctionSymbol, OrderPoly<C>> entry : this.pol.entrySet()) {
            final FunctionSymbol f = entry.getKey();
            final OrderPoly<C> p = entry.getValue();
            final Element inter =
                CPFTag.INTERPRET.create(
                    doc,
                    f.toCPF(doc, xmlMetaData),
                    CPFTag.ARITY.create(doc, f.getArity()),
                    p.toCPF(doc, xmlMetaData, innerRing));
            i.appendChild(inter);
        }
        return CPFTag.ORDERING_CONSTRAINT_PROOF.create(doc, CPFTag.RED_PAIR.create(doc, i));
    }

}
