package aprove.verification.dpframework.Orders.Utility.POLO;

import java.math.*;
import java.util.*;
import java.util.Map.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Afs;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.QActiveCondition.*;
import aprove.verification.dpframework.DPProblem.QApplicativeUsableRules.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;


/**
 * Polynomial interpretation of terms over a certain signature.
 *
 * @author Andreas Capellmann, Carsten Fuhs
 * @version $Id$
 */
public class Interpretation implements Exportable, XMLObligationExportable, CPFAdditional {

    private static Logger log =
        Logger.getLogger("aprove.verification.dpframework.Orders.Utility.POLO.Interpretation");

    // the actual interpretation Pol(f) for function symbols f
    private final Map<FunctionSymbol, VarPolynomial> pol;

    // special ranges for certain Diophantine variables, e.g. those introduced
    // for active (but not for those for non-JAR style autostrict!)
    private final Map<String, BigInteger> specialRanges;

    // cache for interpretations of terms (especially useful when we have
    // non-linear interpretations of function symbols)
    //private Map<Term, VarPolynomial> cache;

    public static final int CONSTANT = -3;
    public static final int INDIVIDUAL = -2;
    public static final int LINEAR = 1;
    public static final int SIMPLE = -1;
    public static final int SIMPLE_MIXED = 0;
    public static final String VARIABLE_PREFIX = "x_";
    public static final String COEFF_PREFIX = "a_";
    public static final String ACTIVE_PREFIX = "b_";
    public static final String AUTOSTRICT_PREFIX = "s_";

    private Citation citation = Citation.POLO;

    private int maxSimpleDegree;
    // maximum degree for SIMPLE and SIMPLE_MIXED to avoid huge polys

    private boolean linearMonotone;
    
    private boolean multilinear;

    private int nextCoeff;

    /**
     * Creates an empty Interpretation
     */
    private Interpretation() {
        this.pol = new LinkedHashMap<FunctionSymbol, VarPolynomial>();
        this.specialRanges = new LinkedHashMap<String, BigInteger>();
        /*this.cache = false ? new HashMap<Term, VarPolynomial>() : null;*/
        this.maxSimpleDegree = 2; // some default value, override later
        this.linearMonotone = false; // some default value, override later
        this.nextCoeff = 1; // we rely on the first value for nextCoeff being 1!
    }

    /**
     * @return a copy of the polynomial interpretation encapsulated by this
     *  Interpretation; the returned map may be modified
     */
    public Map<FunctionSymbol, VarPolynomial> getPol() {
        return new LinkedHashMap<FunctionSymbol, VarPolynomial>(this.pol);
    }

    /**
     * @return the mapping of certain "special" indefinite coefficients
     *  to the range over which they are supposed to be interpreted;
     *  be careful: the encapsulated object itself is returned!
     */
    public Map<String, BigInteger> getSpecialRanges() {
        return this.specialRanges;
    }

    private String getNextCoeff() {
        return Interpretation.COEFF_PREFIX+(this.nextCoeff++);
    }

    private String getNextAutoStrictCoeff() {
        return Interpretation.AUTOSTRICT_PREFIX + (this.nextCoeff++);
    }

    /**
     * Creates a generic (with indefinite coeffs a_i) interpretation of
     * type <code>type</code> for the term
     * constraints <code>constraints</code>.
     *
     * @param constraints we want an interpretation where all occurring
     *  function symbols of constraints are mapped to a polynomial
     * @param degree degree of the generic polynomial interpretations if > 0;
     *  INDIVIDUAL, SIMPLE or SIMPLE_MIXED for the corresponding constants of
     *  Interpretation
     * @param maxSimpleDegree - max degree of monomials for "simple" or
     *  "simple_mixed"
     * @param linearMonotone - require that x^1 has a positive coeff for all
     *  vars x? (otherwise, e.g., x^n can be used for some n > 0 to have the
     *  positive coeff for monotonicity)
     * @return the resulting generic Interpretation for constraints
     */
    public static Interpretation create(final Iterable<Constraint<TRSTerm>> constraints,
            final int degree, final int maxSimpleDegree, final boolean linearMonotone,
            final Abortion aborter) throws AbortionException {

        final Interpretation interpretation =
            new Interpretation();
        interpretation.setMaxSimpleDegree(maxSimpleDegree);
        interpretation.setLinearMonotone(linearMonotone);

        for (final Constraint<TRSTerm> constraint : constraints) {
            interpretation.extend(constraint, degree, aborter);
        }

        return interpretation;
    }

    /**
     * Creates a generic (with indefinite coeffs a_i) interpretation of
     * type <code>type</code> for the term
     * constraints <code>constraints</code>.
     *
     * @param signature - we want an interpretation for these function symbols
     * @param degree - degree of the generic polynomial interpretations if > 0;
     *  INDIVIDUAL, SIMPLE or SIMPLE_MIXED for the corresponding constants of
     *  Interpretation
     * @param maxSimpleDegree - max degree of monomials for "simple" or
     *  "simple_mixed"
     * @param linearMonotone - require that x^1 has a positive coeff for all
     *  vars x? (otherwise, e.g., x^n can be used for some n > 0 to have the
     *  positive coeff for monotonicity)
     * @param multilinear TODO
     * @return the resulting generic Interpretation for constraints
     */
    public static Interpretation createForSignature(final Set<FunctionSymbol> signature,
            final int degree, final int maxSimpleDegree, final boolean linearMonotone,
            boolean multilinear, final Abortion aborter) throws AbortionException {
        final Interpretation interpretation =
            new Interpretation();
        interpretation.setMaxSimpleDegree(maxSimpleDegree);
        interpretation.setLinearMonotone(linearMonotone);
        interpretation.setMultilinear(multilinear);

        for (final FunctionSymbol f : signature) {
            interpretation.extend(f, degree, aborter);
        }
        return interpretation;
    }
    
    
    public static Interpretation createParkForSignature(
    		final Set<FunctionSymbol> signature, 
    		final Set<FunctionSymbol> defSym, 
    		final Abortion aborter) 
    	throws AbortionException {
    	
    	final Interpretation interpretation = new Interpretation();
    	interpretation.setMultilinear(true);
    	
    	for (final FunctionSymbol f : signature) {
    		if (! interpretation.pol.containsKey(f)) {
    			int arity = f.getArity();
	    		if (arity == 0) {
	    			// Constants map to a) if in defSym to Coeff b) if not (normal form) to 1
	    			if (!defSym.contains(f)) {
	    				interpretation.put(f, VarPolynomial.ONE);
	    			} else {
	    				String coeff = interpretation.getNextCoeff();
	    				interpretation.put(f, VarPolynomial.createCoefficient(coeff));
	    			}
	    		} else {
		    		// Constructors of arity > 0 map to product of arguments
	    			if(!defSym.contains(f)) {
	    				final VarPolynomial[] variables = new VarPolynomial[arity];
			    		for (int i = 0; i < arity; ++i) {
			    		    variables[i] = VarPolynomial.createVariable(Interpretation.VARIABLE_PREFIX + (i + 1));
			    		}
			    		
			    		VarPolynomial prod = VarPolynomial.ONE;
			    		for (int i = 0; i < arity; ++i) {
			    	        prod = prod.times(variables[i]);
			    	    }
			    		
			    		interpretation.put(f, prod);
	    			} else {
	    				interpretation.extend(f, -1, aborter);
	    			}
	    		}
    		}
    	}
		return interpretation;
	}
    
   
    public static Interpretation createRepellingForSignature(
            final Set<FunctionSymbol> signature, 
            final Set<FunctionSymbol> defSym, 
            final Abortion aborter) 
        throws AbortionException {
        
        final Interpretation interpretation = new Interpretation();
        interpretation.setMultilinear(true);
        
        for (final FunctionSymbol f : signature) {
            if (! interpretation.pol.containsKey(f)) {
                int arity = f.getArity();
                if (arity == 0) {
                    // Constants map to a) if in defSym to Coeff b) if not (normal form) to 1
                    if (!defSym.contains(f)) {
                        interpretation.put(f, VarPolynomial.ZERO);
                    } else {
                        String coeff = interpretation.getNextCoeff();
                        interpretation.put(f, VarPolynomial.createCoefficient(coeff));
                    }
                } else {
                    // Constructors of arity > 0 map to sum of arguments
                    if(!defSym.contains(f)) {
                        final VarPolynomial[] variables = new VarPolynomial[arity];
                        for (int i = 0; i < arity; ++i) {
                            variables[i] = VarPolynomial.createVariable(Interpretation.VARIABLE_PREFIX + (i + 1));
                        }
                        
                        VarPolynomial sum = VarPolynomial.ZERO;
                        for (int i = 0; i < arity; ++i) {
                            sum = sum.plus(variables[i]);
                        }
                        
                        interpretation.put(f, sum);
                    } else {
                        interpretation.extend(f, -1, aborter);
                    }
                }
            }
        }
        return interpretation;
    }
    
    /**
     * Creates an empty Interpretation
     *
     * @return an empty interpretation
     */
    public static Interpretation create() {
        return new Interpretation();
    }


    /**
     * @param mu - ReplacementMap regarding which mu-monotonicity is to be assured
     *  (symbols of arity n are mapped to subsets of {0, ..., n-1}); use
     *  <code>null</code> to signal that you want strong monotonicity on all
     *  arg positions of all function symbols
     * @returns poly constraints which ensure strong monotonicity of this
     *  for all function symbols, e.g., for
     *  Pol(f(x,y)) = ax^2 + bx + cxy + dy + ey^2 + g, the set
     *  {a + b > 0, d + e > 0} is returned
     */
    public Set<SimplePolyConstraint> getStrongMonotonicityConstraints(final Map<FunctionSymbol, ? extends Set<Integer>> mu) {
        final Set<SimplePolyConstraint> constraints = new LinkedHashSet<SimplePolyConstraint>();
        for (final Entry<FunctionSymbol, VarPolynomial> e : this.pol.entrySet()) {
            final FunctionSymbol f = e.getKey();
            final int arity = f.getArity();
            Set<Integer> strictlyMonotonicArgs = mu == null ? null : mu.get(f);
            // Prevent null pointer exceptions
            if (strictlyMonotonicArgs == null) {
                strictlyMonotonicArgs = new LinkedHashSet<Integer>();
                for (int i = 0; i < arity; i++) {
                    strictlyMonotonicArgs.add(i);
                }
            }
            // construct variables and
            // iterate over all variables/positions
            for (int i = 1; i <= arity; i++) {
                // only enforce strong monotonicity if mu == null
                // or mu requires it for the i-th arg of f
                if (mu == null || strictlyMonotonicArgs.contains(i-1)) {
                    final String x = Interpretation.VARIABLE_PREFIX + i;
                    SimplePolynomial p;
                    if (this.linearMonotone) {
                        p = e.getValue().getCoefficientPoly(x);
                    }
                    else {
                        p = e.getValue().getStrongMonotonicitySum(x);
                    }
                    if (Globals.useAssertions) {
                        assert ! p.isZero();
                    }
                    final SimplePolyConstraint pc = new SimplePolyConstraint(p,
                            ConstraintType.GT);
                    constraints.add(pc);
                }
            }
        }
        return constraints;
    }

    /**
     * @param f - a function symbol that has an interpretation in this
     * @param i - an argument position of f (in {0, ..., f.getArity() - 1})
     * @return a Diophantine constraint whose satisfaction by a Diophantine
     *  model entails that the interpretation of f is indeed strongly
     *  monotonic in its i-th argument
     */
    public Diophantine getStrongMonotonicityConstraint(final FunctionSymbol f,
            final int i) {
        final VarPolynomial fPol = this.pol.get(f);

        // arg i is represented in fPol by x_{i+1}
        final String xForArgI = Interpretation.VARIABLE_PREFIX + (i+1);
        SimplePolynomial p;
        if (this.linearMonotone) {
            p = fPol.getCoefficientPoly(xForArgI);
        }
        else {
            p = fPol.getStrongMonotonicitySum(xForArgI);
        }

        final Diophantine result = Diophantine.create(p, SimplePolynomial.ZERO,
                ConstraintType.GT);
        return result;
    }
    
    /**
     * @param f - a function symbol that has a linear interpretation in this
     * @param i - an argument position of f (in {0, ..., f.getArity() - 1})
     * @return a Diophantine constraint whose satisfaction by a Diophantine
     *  model entails that the interpretation of f is a CPI, i.e., 
     *  Pol(f) = a_1 * x_1 + ... + a_k * x_k + b with a_i in {0,1}
     */
    public Diophantine getCPIConstraintForLinearInterpretation(final FunctionSymbol f, final int i) {
        final VarPolynomial fPol = this.pol.get(f);
        SimplePolynomial p;
        final String xForArgI = Interpretation.VARIABLE_PREFIX + (i+1);
        p = fPol.getCoefficientPoly(xForArgI);
        return Diophantine.create(SimplePolynomial.ONE, p, ConstraintType.GE);
    }
    
    /**
     * @param f - a function symbol that has a linear interpretation in this
     * @param i - an argument position of f (in {0, ..., f.getArity() - 1})
     * @return a Diophantine constraint whose satisfaction by a Diophantine
     *  model entails that the interpretation of f ignores argument i
     */
    public Diophantine getConstantConstraintForLinearInterpretation(final FunctionSymbol f, final int i) {
        final VarPolynomial fPol = this.pol.get(f);
        SimplePolynomial p;
        final String xForArgI = Interpretation.VARIABLE_PREFIX + (i+1);
        p = fPol.getCoefficientPoly(xForArgI);
        return Diophantine.create(SimplePolynomial.ZERO, p, ConstraintType.GE);
    }

    /**
     * @param f - a function symbol that has an interpretation in this
     * @param i - an argument position of f (in {0, ..., f.getArity() - 1})
     * @return a SimplePolyConstraint whose satisfaction by a Diophantine
     *  model entails that the interpretation of f is indeed strongly
     *  monotonic in its i-th argument
     */
    public SimplePolyConstraint getStrongMonotonicityConstraint(final int i,
            final FunctionSymbol f) {
        final VarPolynomial fPol = this.pol.get(f);

        // arg i is represented in fPol by x_{i+1}
        final String xForArgI = Interpretation.VARIABLE_PREFIX + (i+1);
        SimplePolynomial p;
        if (this.linearMonotone) {
            p = fPol.getCoefficientPoly(xForArgI);
        }
        else {
            p = fPol.getStrongMonotonicitySum(xForArgI);
        }
        final SimplePolyConstraint result = new SimplePolyConstraint(p,
                ConstraintType.GT);
        return result;
    }


    /**
     * @param f - a function symbol that must be in the underlying signature;
     *  non-null
     * @param i - an argument position of f (in {0, ..., f.getArity()})
     * @return whether f is guaranteed to be monotonic in its i-th argument
     *  (false negatives may occur)
     */
    public boolean isMonotonicIn(final FunctionSymbol f, final int i) {
        final VarPolynomial fPol = this.pol.get(f);

        // arg i is represented in fPol by x_{i+1}
        final String xForArgI = Interpretation.VARIABLE_PREFIX + (i+1);
        final boolean result = fPol.isStronglyMonotonicIn(xForArgI);
        return result;
    }

    /**
     * @param f - a function symbol that must be in the underlying signature;
     *  non-null
     * @return where f is guaranteed to be monotonic
     *  (false negatives may occur)
     */
    public ImmutableSet<Integer> getMonotonicArgs(final FunctionSymbol f) {
        final VarPolynomial fPol = this.pol.get(f);
        final Set<String> monVars = fPol.getStronglyMonotonicVars();
        final Set<Integer> result = new LinkedHashSet<Integer>();
        final int n = f.getArity();
        for (int i = 0; i < n; ++i) {
            // arg i is represented in fPol by x_{i+1}
            final String varForArgI = Interpretation.VARIABLE_PREFIX + (i+1);
            if (monVars.contains(varForArgI)) {
                result.add(i);
            }
        }
        return ImmutableCreator.create(result);
    }

    /**
     * @return sum of all coeffs of monomials with exactly 1 variable at
     *  some non-zero power
     */
    public SimplePolynomial getMonotonicCoeffsSum() {
        return this.getMonotonicCoeffsSum(null);
    }

    /**
     * @param mu - arguments regarding which mu-monotonicity is to be assured
     *  (symbols of arity n are mapped to subsets of {0, ..., n-1}); use
     *  <code>null</code> to signal that you want strong monotonicity on all
     *  arg positions of all function symbols
     * @return sum of all coeffs of monomials with exactly 1 variable at
     *  some non-zero power
     */
    public SimplePolynomial getMonotonicCoeffsSum(final Map<FunctionSymbol, ? extends Set<Integer>> mu) {
        final List<SimplePolynomial> addends = new ArrayList<SimplePolynomial>();
        for (final Entry<FunctionSymbol, VarPolynomial> e : this.pol.entrySet()) {
            final FunctionSymbol f = e.getKey();
            final int arity = f.getArity();
            final Set<Integer> strictlyMonotonicArgs = mu == null ? null : mu.get(f);
            // construct variables and
            // iterate over all variables/positions
            for (int i = 1; i <= arity; i++) {
                // only enforce strong monotonicity if mu == null
                // or mu requires it for the i-th arg of f
                if (mu == null || strictlyMonotonicArgs.contains(i-1)) {
                    final String x = Interpretation.VARIABLE_PREFIX + i;
                    SimplePolynomial p;
                    if (this.linearMonotone) {
                        p = e.getValue().getCoefficientPoly(x);
                    }
                    else {
                        p = e.getValue().getStrongMonotonicitySum(x);
                    }

                    if (Globals.useAssertions) {
                        assert ! p.isZero();
                    }
                }
            }
        }
        final SimplePolynomial result = SimplePolynomial.plus(addends);
        return result;
    }


    /**
     * Sets the maximum degree used for simple and simple mixed
     * interpretations.
     *
     * @param maxDegree the degree to set, > 0
     */
    public void setMaxSimpleDegree(int maxDegree) {
        if (maxDegree < 1) {
            maxDegree = 1;
        }
        this.maxSimpleDegree = maxDegree;
    }

    /**
     * @return the maximum degree of some polynomial contained by this
     *  (where e.g. x^2*y^3 has degree 2+3 = 5)
     */
    public int getDegree() {
        int res = 0;
        for (final Entry<FunctionSymbol, VarPolynomial> e : this.pol.entrySet()) {
            final int degree = e.getValue().getDegree();
            if (degree > res) {
                res = degree;
            }
        }
        return res;
    }
    
    /**
     * @param sig - the signature to consider
     * @return the maximum degree of some polynomial contained by this
     * only considering the signature given as parameter
     *  (where e.g. x^2*y^3 has degree 2+3 = 5)
     */
    public int getDegree(Set<FunctionSymbol> sig) {
        int res = 0;
        for (final Entry<FunctionSymbol, VarPolynomial> e : this.pol.entrySet()) {
            final int degree = e.getValue().getDegree();
            final FunctionSymbol fun = e.getKey();
            if (degree > res && sig.contains(fun)) {
                res = degree;
            }
        }
        return res;
    }

    public SimplePolynomial extendByActiveCondition() {
        final String newActiveCoeff = Interpretation.ACTIVE_PREFIX+(this.nextCoeff++);
        this.specialRanges.put(newActiveCoeff, BigInteger.ONE);
        return SimplePolynomial.create(newActiveCoeff);
    }

    /**
     * Extends this for the new function symbols of the term constraint
     * constraint.
     *
     * @param constraint this is to be extended for constraint
     * @param degree the degree of the desired interpretation if > 0
     *  or one of SIMPLE, SIMPLE_MIXED, INDIVIDUAL
     */
    public void extend(final Constraint<TRSTerm> constraint, final int degree,
            final Abortion aborter) throws AbortionException {
        for (final FunctionSymbol fSym : constraint.getLeft().getFunctionSymbols()) {
            this.extend(fSym, degree, aborter);
        }
        for (final FunctionSymbol fSym : constraint.getRight().getFunctionSymbols()) {
            this.extend(fSym, degree, aborter);
        }
    }

    /**
     * Extends this for symbol if symbol does not already have
     * an interpretation in this.
     *
     * @param symbol the function symbol for which we want an interpretation.
     * @param degree the degree of the desired interpretation if > 0
     *  or one of SIMPLE, SIMPLE_MIXED, INDIVIDUAL
     */
    public void extend(final FunctionSymbol symbol, final int degree,
            final Abortion aborter) throws AbortionException {
        if (! this.pol.containsKey(symbol)) {
            this.pol.put(symbol, this.getPolynomialFromFunction(symbol, degree, aborter));
        }
    }
    
    /**
     * extends a Interpretation for all functions
     * determined in the afs, such that if a
     * term is from this signature we have
     * afs(s) >/= emb afs(t) implies Pol(s) >/= Pol(t).
     * To ensure this, however, the returned constraints
     * have to be satisfied.
     *
     * Note, that all symbols in the afs must be new
     * in this interpretation.
     *
     * @param afs
     * @return
     */
    public Set<VarPolyConstraint> extendForEmb(final Afs afs) {
        final Set<VarPolyConstraint> constraints = new LinkedHashSet<VarPolyConstraint>();
        f_Loop:
        for (final Triple<FunctionSymbol, YNM[], Boolean> filtering : afs.getFilterings()) {
            final boolean collapsing = filtering.z.booleanValue();
            final FunctionSymbol f = filtering.x;
            final YNM[] map = filtering.y;
            final int n = map.length;
            if (Globals.useAssertions) {
                assert(n == f.getArity());
            }
            if (collapsing) {
                for (int i = 0; i<n; i++) {
                    if (map[i] == YNM.YES) {
                        final VarPolynomial old = this.pol.put(f, VarPolynomial.createVariable(Interpretation.VARIABLE_PREFIX+(i+1)));
                        if (Globals.useAssertions) {
                            assert(old == null);
                        }
                        continue f_Loop;
                    }
                }
                assert(false);
            } else {
                String coeff = this.getNextCoeff();
                VarPolynomial inter = VarPolynomial.createCoefficient(coeff);
                constraints.add(new VarPolyConstraint(inter, ConstraintType.GT));

                for (int i = 0; i<n; i++) {
                    if (map[i] == YNM.YES) {
                        coeff = this.getNextCoeff();
                        final VarPolynomial c_x_i = VarPolynomial.createCoefficient(coeff);
                        constraints.add(new VarPolyConstraint(c_x_i, ConstraintType.GT));
                        inter = inter.plus(c_x_i.times(VarPolynomial.createVariable(Interpretation.VARIABLE_PREFIX+(i+1))));
                    }
                }
                inter = this.pol.put(f, inter);
                if (Globals.useAssertions) {
                    assert(inter == null);
                }
            }
        }
        return constraints;
    }


    /**
     * Maps symbol to polynomial in this if symbol does not already have
     * an interpretation in this.
     *
     * @param symbol the function symbol which we want to interpret
     *  as polynomial
     * @param polynomial the proposed polynomial interpretation for symbol
     */
    public void extend(final FunctionSymbol symbol, final VarPolynomial polynomial) {
        if (this.pol.containsKey(symbol)) {
            return;
        }
        this.pol.put(symbol, polynomial);
    }


    /**
     * Calculates the polynomial interpretation of a term constraint based on
     * the present interpretation of the signature.
     *
     * @param constraint
     *            the term constraint to convert
     * @return the polynomial interpretation of the given term constraint
     */
    public VarPolyConstraint getPolynomialConstraint(final Constraint<TRSTerm> constraint, final Abortion aborter) throws AbortionException {
        VarPolynomial polynomial = this.interpretTerm(constraint.getLeft(), aborter);
        polynomial = polynomial.minus(this.interpretTerm(constraint.getRight(), aborter));

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
            throw new RuntimeException("Can't make a polyconstraint type out of "
                            + constraint.getType() + "!");
        }
        return new VarPolyConstraint(polynomial, type);
    }

    /**
     * Calculates the polynomial interpretation of a rule based on the
     * present interpretation of the signature.
     *
     * @param rule to be converted to a VarPolyConstraint
     * @param type type of the resulting constraint (GT/GE/EQ)
     * @return a VarPolyConstraint which encodes the polynomial
     *  interpretation of rule of type type.
     */
    public VarPolyConstraint getPolynomialConstraint(final Rule rule, final ConstraintType type, final Abortion aborter) throws AbortionException {
        final VarPolynomial left = this.interpretTerm(rule.getLeft(), aborter);
        final VarPolynomial right = this.interpretTerm(rule.getRight(), aborter);
        final VarPolynomial poly = left.minus(right);
        return new VarPolyConstraint(poly, type);
    }

    /**
     * Encodes the constraints for P into one big formula.
     * If allStrict is true then all constraints in pConstraints should encode
     * s > t, and if allStrict is false then all constraints in pConstraints should
     * encode s >= t.
     *
     * @param allStrict: if true, then the pConstraints are just converted into one big conjunction.
     * Otherwise, pConstraints are converted into the conjunction of pConstraints and
     * "s1 > t1 or ... or sn > tn"
     */
    public Formula<Diophantine> encodePConstraints(
            final Collection<Constraint<TRSTerm>> pConstraints,
            final boolean allStrict,
            final FormulaFactory<Diophantine> factory,
            final Abortion aborter) throws AbortionException {
        final List<Formula<Diophantine>> conjuncts = new ArrayList<Formula<Diophantine>>();
        if (allStrict) {
            for (final Constraint<TRSTerm> pCons : pConstraints) {
                this.producePformula(pCons, conjuncts, true, factory, aborter);
            }
        } else {
            final List<Formula<Diophantine>> disjuncts = new ArrayList<Formula<Diophantine>>();
            for (final Constraint<TRSTerm> pCons : pConstraints) {
                disjuncts.add(this.producePformula(pCons, conjuncts, false, factory, aborter));
            }
            conjuncts.add(factory.buildOr(disjuncts));
        }

        return factory.buildAnd(conjuncts);
    }

    /**
     * Converts a set of conditional contraints over terms into a large conjunction of implications of diophantine constraints.
     * Moreover, the mapping from AfsProp-variables to Diophantine-variables is also returned.
     */
    public Pair<Formula<Diophantine>, Map<aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<AfsProp>,
                                           aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<Diophantine>>> encodeRuleConstraints(
            final Collection<Pair<Constraint<TRSTerm>,
            aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<AfsProp>>> rules,
            final FormulaFactory<Diophantine> factory, final Abortion aborter) throws AbortionException {
        // the final variable mapping
        Map<aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<AfsProp>,aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<Diophantine>> varMap;
        varMap = new HashMap<aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<AfsProp>, aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<Diophantine>>();

        // the final conjunction
        final List<Formula<Diophantine>> conjuncts = new ArrayList<Formula<Diophantine>>();

        // a temporary set to collect all intermediate simplyPolyConstraints
        // will be emptied all the time
        final Collection<SimplePolyConstraint> tmp = new ArrayList<SimplePolyConstraint>();

        // now process all rules
        for (final Pair<Constraint<TRSTerm>, aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<AfsProp>> usableCond : rules) {
            final Constraint<TRSTerm> usableConstraint = usableCond.x;
            // convert the constraint resulting in "c1 and ... and cn"
            this.produceSimplePolyConstraints(usableConstraint, tmp, aborter);
            // and get corresponding variable over diophantine logic
            final aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<AfsProp> cond = usableCond.y;
            aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<Diophantine> condD = varMap.get(cond);
            if (condD == null) {
                condD = factory.buildVariable();
                varMap.put(cond, condD);
            }
            // now encode "condD -> (c1 and ... and cn)"
            // by "(condD -> c1) and ... and (condD -> cn)"
            for (final SimplePolyConstraint sp : tmp) {
                final Diophantine dio = Diophantine.create(sp.getPolynomial(), sp.getType());
                Formula<Diophantine> fdio = factory.buildTheoryAtom(dio);
                fdio = factory.buildImplication(condD, fdio);
                conjuncts.add(fdio);
            }
            tmp.clear();
        }
        final Formula<Diophantine> resFormula = factory.buildAnd(conjuncts);
        return new Pair<Formula<Diophantine>, Map<aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<AfsProp>,aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<Diophantine>>>(resFormula, varMap);
    }

    /**
     * Encodes the formula over afs-properties into formula over
     * diophantine. E.g. "0 in pi(f)" will be encoded as "a2 > 0 or a3 > 0" if Pol(f(x1,x2)) = a1 + a2x1 + a3x1x2 + a4x2
     * @param varMap Here the variable mapping will be stored and extended, must be non-null.
     */
    public Formula<Diophantine> encodeActiveConstraint(
            final Formula<AfsProp> formula,
            final Map<aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<AfsProp>,
            aprove.verification.oldframework.PropositionalLogic.Formulae.Variable<Diophantine>> varMap,
            final FormulaFactory<Diophantine> factory
            ) {
        final TheoryConverter<AfsProp, Diophantine> converter = new TheoryConverter<AfsProp, Diophantine>() {
                @Override
                public Formula<Diophantine> convert(final AfsProp fi) {
                        final FunctionSymbol f = fi.f;
                        final int i = fi.i;

                        final VarPolynomial pol = Interpretation.this.pol.get(f);
                        final String var = Interpretation.VARIABLE_PREFIX+(i+1);
                        final List<SimplePolynomial> coeffPolies = pol.getListOfCoefficientPolys(var);
                        if (coeffPolies.size() == 1) {
                            final SimplePolynomial sp = coeffPolies.iterator().next();
                            return factory.buildTheoryAtom(Diophantine.create(sp, ConstraintType.GT));
                        } else if (coeffPolies.size() > 0) {
                            final List<Formula<Diophantine>> disjuncts = new ArrayList<Formula<Diophantine>>(coeffPolies.size());
                            for (final SimplePolynomial sp : coeffPolies) {
                                disjuncts.add(factory.buildTheoryAtom(Diophantine.create(sp, ConstraintType.GT)));
                            }
                            return factory.buildOr(disjuncts);
                        } else {
                            return factory.buildConstant(false);
                        }
                }
        };


        TheoryConverterVisitor<AfsProp, Diophantine> visitor;
        visitor = new TheoryConverterVisitor<AfsProp, Diophantine>(factory, converter, varMap);

        return formula.apply(visitor);
    }

    /**
     * Converts a term-constraint into the set of all constraints that have to be
     * satisfied to satisfy the constraints. These constraints will be added to addHere.
     */
    private void produceSimplePolyConstraints(final Constraint<TRSTerm> constraint, final Collection<SimplePolyConstraint> addHere, final Abortion aborter) throws AbortionException {
        final VarPolyConstraint cons = this.getPolynomialConstraint(constraint, aborter);
        addHere.addAll(cons.createCoefficientConstraints());
    }

    /**
     * Converts a term-constraint into a conjunction of diophantine constraints. All conjuncts
     * will be added into the Collection conjuncts. Moreover, if allStrict is false, then
     * the constraint for ensuring the strict decrease is returned.
     */
    private Formula<Diophantine> producePformula(final Constraint<TRSTerm> constraint, final Collection<Formula<Diophantine>> conjuncts, final boolean allStrict, final FormulaFactory<Diophantine> factory, final Abortion aborter) throws AbortionException {
        final VarPolyConstraint cons = this.getPolynomialConstraint(constraint, aborter);
        for (final SimplePolyConstraint spc : cons.createCoefficientConstraints()) {
            conjuncts.add(factory.buildTheoryAtom(Diophantine.create(spc.getPolynomial(), spc.getType())));
        }
        if (allStrict) {
            return null;
        } else {
            return factory.buildTheoryAtom(Diophantine.create(cons.getPolynomial().getConstantPart(), ConstraintType.GT));
        }
    }

    public Pair<Set<SimplePolyConstraint>, Set<VarPolyConstraint>> getActiveRuleConstraints(final Map<? extends GeneralizedRule, QActiveCondition> usableRules, final Map<Equation, QActiveCondition> usableEqns, final int degree, final Abortion aborter) throws AbortionException {
        // build active usable rules constraints
        Map<QActiveCondition, SimplePolynomial> activeConditions;
        final Set<SimplePolyConstraint> activeConstraints = new LinkedHashSet<SimplePolyConstraint>();
        final Set<VarPolyConstraint> ruleConstraints = new LinkedHashSet<VarPolyConstraint>();
        activeConditions = new LinkedHashMap<QActiveCondition, SimplePolynomial>();

        // extend signature
        for (final GeneralizedRule rule : usableRules.keySet()) {
            for (final aprove.verification.oldframework.BasicStructures.FunctionSymbol f : rule.getFunctionSymbols()) {
                this.extend(f, degree, aborter);
            }
        }
        if (usableEqns != null) {
            for (final Equation eqn : usableEqns.keySet()) {
                for (final aprove.verification.oldframework.BasicStructures.FunctionSymbol f : eqn.getFunctionSymbols()) {
                    this.extend(f, degree, aborter);
                }
            }
        }

        // build constraints for activation conditions and rules
        for (final Map.Entry<? extends GeneralizedRule, QActiveCondition> usable : usableRules.entrySet()) {
            final QActiveCondition qac = usable.getValue();
            final boolean isTrue = qac == QActiveCondition.TRUE;
            SimplePolynomial activeCondition;
            if (isTrue) {
                activeCondition = null;
            } else {
                activeCondition = this.getActiveCondition(qac, activeConstraints, activeConditions, aborter);
            }

            final GeneralizedRule rule = usable.getKey();
            final TRSTerm left = rule.getLeft();
            final TRSTerm right = rule.getRight();

            // build rule constraint
            VarPolynomial constraint = this.interpretTerm(left, aborter).minus(this.interpretTerm(right, aborter));
            aborter.checkAbortion();

            // multiply it with active condition
            if (!isTrue) {
                constraint = constraint.times(activeCondition);
            }
            ruleConstraints.add(new VarPolyConstraint(constraint, ConstraintType.GE));
        }

        // build constraints for activation conditions and equations
        if (usableEqns != null) {
            Map<FunctionSymbol, SimplePolynomial> acSyms, cSyms;
            // Associative/commutative symbols and their activation conditions.
            // If a symbol is just associative, it will be treated
            // as though it were AC because we are going to generate
            // constraints for AC then.

            acSyms = new LinkedHashMap<FunctionSymbol, SimplePolynomial>();
            cSyms = new LinkedHashMap<FunctionSymbol, SimplePolynomial>();

            // compute active conditions and collect A/C function symbols
            for (final Map.Entry<Equation, QActiveCondition> usable : usableEqns.entrySet()) {
                final QActiveCondition qac = usable.getValue();
                final boolean isTrue = qac == QActiveCondition.TRUE;
                SimplePolynomial activeCondition;
                if (isTrue) {
                    activeCondition = null;
                } else {
                    activeCondition = this.getActiveCondition(qac, activeConstraints, activeConditions, aborter);
                }

                final Equation eqn = usable.getKey();
                final FunctionSymbol f = ((TRSFunctionApplication) eqn.getLeft()).getRootSymbol();
                if (eqn.checkAEquation()) {
                    acSyms.put(f, activeCondition);
                }
                else if (eqn.checkCEquation()) {
                    cSyms.put(f, activeCondition);
                }
                else {
                    if (Globals.useAssertions) {
                        assert false : "Every usable equation should be associative or commutative (as of now)!";
                    }
                }
                aborter.checkAbortion();
            }

            // now remove associative symbols from cSyms ...
            cSyms.keySet().removeAll(acSyms.keySet());

            // ... and build the actual constraints with activation conds
            for (final Entry<FunctionSymbol, SimplePolynomial> e : acSyms.entrySet()) {
                final FunctionSymbol f = e.getKey();
                final SimplePolynomial activationPoly = e.getValue();
                final Collection<SimplePolyConstraint> spcs = this.getACPolyConstraints(f);
                if (activationPoly == null) {
                    activeConstraints.addAll(spcs);
                }
                else {
                    for (final SimplePolyConstraint spc : spcs) {
                        final SimplePolynomial newPoly = spc.getPolynomial().times(activationPoly);
                        SimplePolyConstraint newSpc;
                        newSpc = new SimplePolyConstraint(newPoly, spc.getType());
                        activeConstraints.add(newSpc);
                    }
                }
            }
            for (final Entry<FunctionSymbol, SimplePolynomial> e : cSyms.entrySet()) {
                final FunctionSymbol f = e.getKey();
                final SimplePolynomial activationPoly = e.getValue();
                final Collection<SimplePolyConstraint> spcs = this.getCPolyConstraints(f);
                if (activationPoly == null) {
                    activeConstraints.addAll(spcs);
                }
                else {
                    for (final SimplePolyConstraint spc : spcs) {
                        final SimplePolynomial newPoly = spc.getPolynomial().times(activationPoly);
                        SimplePolyConstraint newSpc;
                        newSpc = new SimplePolyConstraint(newPoly, spc.getType());
                        activeConstraints.add(newSpc);
                    }
                }
            }

        }
        return new Pair<Set<SimplePolyConstraint>, Set<VarPolyConstraint>>(activeConstraints, ruleConstraints);
    }

    private SimplePolynomial getActiveCondition(final QActiveCondition qac, final Set<SimplePolyConstraint> activeConstraints, final Map<QActiveCondition, SimplePolynomial> cache, final Abortion aborter) throws AbortionException {
        SimplePolynomial activeCondition = cache.get(qac);

        // do we already have an active Condition or do we need to create a new one?
        if (activeCondition == null) {
            // we need a new one

            // get fresh coefficient for active condition
            activeCondition = this.extendByActiveCondition();
            cache.put(qac, activeCondition);

            // require "active condition <= 1"
            final SimplePolynomial validCondition = SimplePolynomial.ONE.minus(activeCondition);
            activeConstraints.add(new SimplePolyConstraint(validCondition, ConstraintType.GE));

            // if we have f/1^g/2 v h/3 then build "(activeCondition - 1) * f/1 * g/2 = 0" and
            // "(activeCondition - 1) * h/3 = 0"
            this.addActiveConstraints(activeConstraints, qac, activeCondition, aborter);

        }

        return activeCondition;

    }


    /**
     * adds for a given activation condition and the corresponding coefficient "activeCondition" those
     * constraints to the "constraints" set such that the activeCondition = 1 is enforced if the
     * activation condition evaluates to true.
     * @param constraints we add the new constraints to this set
     * @param condition this is the qactive condition
     * @param activeCondition the coefficient which should store "condition is active"
     */
    public void addActiveConstraints(final Set<SimplePolyConstraint> constraints, final QActiveCondition condition, SimplePolynomial activeCondition, final Abortion aborter) throws AbortionException {
        activeCondition = activeCondition.plus(SimplePolynomial.MINUS_ONE);
        nextAndConditions:
        for (final Set<Pair<FunctionSymbol, Integer>> andCondition : condition.getSetRepresentation()) {
            aborter.checkAbortion();
            SimplePolynomial product = SimplePolynomial.ONE;
            for (final Pair<FunctionSymbol, Integer> pair : andCondition) {
                final VarPolynomial pol = this.pol.get(pair.x);
                final int position = pair.y.intValue();
                final String var = Interpretation.VARIABLE_PREFIX+(position+1);
                final SimplePolynomial coeffPoly = pol.getSumOfCoefficientPolys(var);
                final BigInteger constantPart = coeffPoly.getNumericalAddend();
                if (constantPart.signum() > 0) {
                    continue;
                } else {
                    if (Globals.useAssertions) {
                        assert(constantPart.signum() == 0);
                    }
                    if (coeffPoly.equals(SimplePolynomial.ZERO)) {
                        continue nextAndConditions;
                    }
                    product = product.times(coeffPoly);
                }
            }

            if (product.getNumericalAddend().signum() > 0) {
                constraints.add(new SimplePolyConstraint(activeCondition, ConstraintType.EQ));
                return;
            } else {
                constraints.add(new SimplePolyConstraint(activeCondition.times(product), ConstraintType.EQ));
            }
        }
    }


    /**
     * computes a polynomial which is larger 0 iff the condition is satisfied.
     * @param condition
     * @return
     */
    public SimplePolynomial getActiveConstraint(final QActiveCondition condition) {
        SimplePolynomial sum = SimplePolynomial.ZERO;
        nextAndConditions:
        for (final Set<Pair<FunctionSymbol, Integer>> andCondition : condition.getSetRepresentation()) {
            SimplePolynomial product = SimplePolynomial.ONE;
            for (final Pair<FunctionSymbol, Integer> pair : andCondition) {
                final FunctionSymbol f = pair.x;
                final VarPolynomial pol = this.pol.get(f);
                final int position = pair.y.intValue();
                final String var = Interpretation.VARIABLE_PREFIX+(position+1);
                final SimplePolynomial coeffPoly = pol.getSumOfCoefficientPolys(var);
                final BigInteger constantPart = coeffPoly.getNumericalAddend();
                if (constantPart.signum() > 0) {
                    continue;
                } else {
                    if (Globals.useAssertions) {
                        assert(constantPart.signum() == 0);
                    }
                    if (coeffPoly.equals(SimplePolynomial.ZERO)) {
                        continue nextAndConditions;
                    }
                    product = product.times(coeffPoly);
                }
            }

            if (product.getNumericalAddend().signum() > 0) {
                return SimplePolynomial.ONE;
            }

            sum = sum.plus(product);
        }
        return sum;
    }

    /**
     * Calculates the polynomial interpretation of a set of term constraints
     * based on the present interpretation of the signature.
     *
     * @param constraints
     *            set of term constraints to convert
     * @param aborter
     * @return the polynomial interpretation of the given term constraints
     */
    public Set<VarPolyConstraint> getPolynomialConstraints(final Set<Constraint<TRSTerm>> constraints,
            final Abortion aborter) throws AbortionException {
        final Set<VarPolyConstraint> cs = new LinkedHashSet<VarPolyConstraint>();
        Interpretation.log.log(Level.CONFIG, "Creating polynomial constraints for "
                + constraints.size() + " term constraints...\n");
        for (final Constraint<TRSTerm> constraint : constraints) {
            Interpretation.log.log(Level.FINE, "Processing constraint {0}.\n", constraint);
            final VarPolyConstraint newConstraint = this.getPolynomialConstraint(constraint, aborter);
            cs.add(newConstraint);
        }

        return cs;
    }


    /**
     * Adds the autoStrictConstraint (sum of the polys of poloConstraints with
     * all variables replaced by 0 to be > 0) to poloConstraints.
     *
     * @param poloConstraints the autoStrictConstraint is to be generated and
     *  added to poloConstraints
     */
    public void addAutoStrictConstraint(final Set<VarPolyConstraint> poloConstraints) {
        this.addAutoStrictConstraint(poloConstraints, true);
    }

    /**
     * Makes sure that one of the constraints of poloConstraints will be
     * oriented strictly if possible.
     *
     * @param poloConstraints - set of VPCs of type GE of which at least one
     *  is to be oriented strictly
     * @param jarAuto - true: no new Diophantine variables (-> JAR'06 paper)<br>
     *                 false: introduce new Diophantine variables, so the
     *                        resulting constraints are not that big
     * @return pair:<br>
     *  (1) SimplePolynomial such that maximizing it means
     *      orienting the highest number of term constraints strictly<br>
     *  (2) newly introduced Diophantine variables, tell the searchAlg that
     *      they should have range 1!
     */
    public Pair<SimplePolynomial, String[]> addAutoStrictConstraint(final Set<VarPolyConstraint> poloConstraints,
            final boolean jarAuto) {
        if (jarAuto) {
            final SimplePolynomial maxMe = this.addAutoStrictConstraintJAR06(poloConstraints,poloConstraints);
            return new Pair<SimplePolynomial, String[]>(maxMe, new String[0]);
        }
        else {
            final Triple<Set<VarPolyConstraint>, String[], SimplePolynomial> newCsAndAutoIndefs =
                this.toAutoStrictWithNewIndefinites(poloConstraints);
            poloConstraints.clear();
            poloConstraints.addAll(newCsAndAutoIndefs.x);
            return new Pair<SimplePolynomial, String[]>(newCsAndAutoIndefs.z,
                    newCsAndAutoIndefs.y);
        }
    }


    /**
     * builds from the first given constraints the auto-Strict constraint
     * and adds this to the second constraints (destructive):
     * from s1-t1 >/>= 0,..., sn-tn >/>= 0 build
     *  (s1-t1 + ... + sn-tn)(0,...,0) > 0
     *
     * This is described in more detail in the JAR'06 paper.
     *
     * @param poloFromConstraints from here we construct the autoStrictConstraint
     * @param poloToConstraints the autoStrictConstraint is added here
     * @return the polynomial that corresponds to the autostrict constraint
     */
    private SimplePolynomial addAutoStrictConstraintJAR06(final Set<VarPolyConstraint> poloFromConstraints,
            final Set<VarPolyConstraint> poloToConstraints) {
        SimplePolynomial poly = SimplePolynomial.ZERO;
        // sum up everything
        for (final VarPolyConstraint fromConstraint : poloFromConstraints) {
            final SimplePolynomial constantPoly = fromConstraint.getPolynomial().getConstantPart();
            if (! constantPoly.equals(SimplePolynomial.ZERO)) {
                poly = poly.plus(constantPoly);
            }
        }
        VarPolynomial varPoly;
        varPoly = VarPolynomial.create(poly);
        final VarPolyConstraint addMe = new VarPolyConstraint(varPoly, ConstraintType.GT);
        poloToConstraints.add(addMe);
        return poly;
    }

    /**
     * Given p_1 - q_1 >= 0, ..., p_n - q_n >= 0, we get
     * s_1 + ... + s_n - 1 >= 0, p_1 - q_1 - s_1 >= 0, ...,
     *                           p_n - q_n - s_1 >= 0;
     * here, it suffices to have the s_i range over {0, 1}
     * (this information is not stored inside this, but the
     * names of the s_i are returned to the caller)
     *
     * @param vpcs - constraints of type GE for which autostrict constraints
     *  are supposed to be generated
     * @return (1) an autostrict version of vpcs that may contain some new
     *  indefinite coefficients aka Diophantine variables<br>
     *         (2) the new Diophantine variables<br>
     *         (3) the polynomial s_1 + ... + s_n; maximizing it means
     *  orienting the highest number of term constraints strictly
     */
    private Triple<Set<VarPolyConstraint>, String[], SimplePolynomial> toAutoStrictWithNewIndefinites(final Set<VarPolyConstraint> vpcs) {
        final int numberOfVPCs = vpcs.size();
        final String[] autostrictCoeffs = new String[numberOfVPCs];

        // first of all, state s_1 + ... + s_n - 1 >= 0;
        final Map<IndefinitePart, BigInteger> simpleMonomials = new LinkedHashMap<IndefinitePart, BigInteger>(numberOfVPCs + 1);
        for (int i = 0; i < numberOfVPCs; ++i) {
            autostrictCoeffs[i] = this.getNextAutoStrictCoeff();
            final IndefinitePart iPart = IndefinitePart.create(autostrictCoeffs[i], 1);
            simpleMonomials.put(iPart, BigInteger.ONE);
        }

        // interlude: use gathered IParts for 2nd component of result
        Map<IndefinitePart, BigInteger> simpleMonomialsForSumOfAuto;
        simpleMonomialsForSumOfAuto = new LinkedHashMap<IndefinitePart, BigInteger>(simpleMonomials);
        final SimplePolynomial sumOfAutostrictCoeffs = SimplePolynomial.create(simpleMonomialsForSumOfAuto);

        // now finish construction of s_1 + ... + s_n - 1 >= 0;
        simpleMonomials.put(IndefinitePart.ONE, BigInteger.valueOf(-1));
        final VarPolynomial sumGE1 = VarPolynomial.create(SimplePolynomial.create(simpleMonomials));

        final Set<VarPolyConstraint> result = new LinkedHashSet<VarPolyConstraint>(numberOfVPCs + 1);
        result.add(new VarPolyConstraint(sumGE1, ConstraintType.GE));

        // p_i - q_i >(=) 0 becomes p_i - q_i - s_i >= 0
        int i = 0;
        for (final VarPolyConstraint vpc : vpcs) {
            if (Globals.useAssertions) {
                assert vpc.getType() == ConstraintType.GE;
            }
            final VarPolynomial subtrahend = VarPolynomial.createCoefficient(autostrictCoeffs[i]);
            ++i;
            final VarPolynomial newVp = vpc.getPolynomial().minus(subtrahend);
            final VarPolyConstraint newVpc = new VarPolyConstraint(newVp, vpc.getType());
            result.add(newVpc);
        }
        return new Triple<Set<VarPolyConstraint>, String[], SimplePolynomial>(result,
                autostrictCoeffs, sumOfAutostrictCoeffs);
    }

    /**
     * Convenience method
     * @param fs
     * @return
     */
    public Set<SimplePolyConstraint> getACPolyConstraints(final Collection<FunctionSymbol> fs, final int degree) {
        final Set<SimplePolyConstraint> spcs = new LinkedHashSet<SimplePolyConstraint>();
        for (final FunctionSymbol f : fs) {
            spcs.addAll(this.getACPolyConstraints(f));
        }
        return spcs;
    }

    /**
     * For a binary FunctionSymbol f, return a set of SimplePolyConstraints
     * that suffices for enforcing that the corresponding POLO is compatible
     * with it being AC. This way, we can avoid having to deal with the
     * individual AC equations.
     *
     * @param f  a binary FunctionSymbol, must occur in the signature of this
     * @return SPCs that state that f is AC
     */
    public Set<SimplePolyConstraint> getACPolyConstraints(final FunctionSymbol f) {
        if (Globals.useAssertions) {
            assert f.getArity() == 2;
            assert this.pol.containsKey(f);
        }

        final VarPolynomial varPoly = this.pol.get(f);
        final String x1 = Interpretation.VARIABLE_PREFIX + "1";
        final String x2 = Interpretation.VARIABLE_PREFIX + "2";

        final Map<String, Integer> x1x2Map = new LinkedHashMap<String, Integer>(2);
        x1x2Map.put(x1, 1);
        x1x2Map.put(x2, 1);
        final IndefinitePart x1x2 = IndefinitePart.create(x1x2Map);


        final SimplePolynomial x1CoeffPoly = varPoly.getCoefficientPoly(x1);
        final SimplePolynomial x2CoeffPoly = varPoly.getCoefficientPoly(x2);
        final SimplePolynomial x1x2CoeffPoly = varPoly.getCoefficientPoly(x1x2);

        SimplePolyConstraint spc1, spc2;

        // x_1 and x_2 must have the same coefficient (in all cases!)
        spc1 = new SimplePolyConstraint(x1CoeffPoly.minus(x2CoeffPoly),
                ConstraintType.EQ);
        final Set<SimplePolyConstraint> result = new LinkedHashSet<SimplePolyConstraint>(2);
        result.add(spc1);



        final int degree = Interpretation.computeDegreeOfBinaryInterpretation(varPoly);
        switch (degree) {
        case LINEAR : {
            spc2 = new SimplePolyConstraint(SimplePolynomial.ONE.minus(x1CoeffPoly),
                    ConstraintType.GE);
            // over the naturals, "1 - a >= 0" is equivalent to "a = a^2"
            result.add(spc2);
            break;
        }
        case 2 : {
            final Map<String, Integer> x1sqMap = new LinkedHashMap<String, Integer>(1);
            x1sqMap.put(x1, 2);
            final IndefinitePart x1sq = IndefinitePart.create(x1sqMap);
            final SimplePolynomial x1sqCoeff = varPoly.getCoefficientPoly(x1sq);
            final Map<String, Integer> x2sqMap = new LinkedHashMap<String, Integer>(1);
            x2sqMap.put(x2, 2);
            final IndefinitePart x2sq = IndefinitePart.create(x2sqMap);
            final SimplePolynomial x2sqCoeff = varPoly.getCoefficientPoly(x2sq);

            result.add(new SimplePolyConstraint(x1sqCoeff, ConstraintType.EQ));
            result.add(new SimplePolyConstraint(x2sqCoeff, ConstraintType.EQ));

            final SimplePolynomial constantCoeffPoly = varPoly.getConstantPart();
            SimplePolynomial sp = x1x2CoeffPoly.times(constantCoeffPoly);
            sp = sp.plus(x1CoeffPoly);
            sp = sp.minus(x1CoeffPoly.times(x1CoeffPoly));
            spc2 = new SimplePolyConstraint(sp, ConstraintType.EQ);
            result.add(spc2);
            break;
        }
        case SIMPLE :
        case SIMPLE_MIXED : {
            final SimplePolynomial constantCoeffPoly = varPoly.getConstantPart();
            SimplePolynomial sp = x1x2CoeffPoly.times(constantCoeffPoly);
            sp = sp.plus(x1CoeffPoly);
            sp = sp.minus(x1CoeffPoly.times(x1CoeffPoly));
            spc2 = new SimplePolyConstraint(sp, ConstraintType.EQ);
            result.add(spc2);
            break;
        }
        default :
            throw new UnsupportedOperationException("cannot get AC SPCs for degree " + degree + " (yet)");
        }

        return result;
    }

    /**
     * Convenience method
     * @param fs
     * @return
     */
    public Set<SimplePolyConstraint> getCPolyConstraints(final Collection<FunctionSymbol> fs) {
        final Set<SimplePolyConstraint> spcs = new LinkedHashSet<SimplePolyConstraint>();
        for (final FunctionSymbol f : fs) {
            spcs.addAll(this.getACPolyConstraints(f));
        }
        return spcs;
    }


    /**
     * For a binary FunctionSymbol f, return a set of SimplePolyConstraints
     * that suffices for enforcing that the corresponding POLO is compatible
     * with it being C. This way, we can avoid having to deal with the
     * individual C equations.
     *
     * @param f  a binary FunctionSymbol, must occur in the signature of this
     * @return SPCs that state that f is C
     */
    public Set<SimplePolyConstraint> getCPolyConstraints(final FunctionSymbol f) {
        if (Globals.useAssertions) {
            assert f.getArity() == 2;
            assert this.pol.containsKey(f);
        }

        final VarPolynomial varPoly = this.pol.get(f);
        final String x1 = Interpretation.VARIABLE_PREFIX + "1";
        final String x2 = Interpretation.VARIABLE_PREFIX + "2";

        final SimplePolynomial x1CoeffPoly = varPoly.getCoefficientPoly(x1);
        final SimplePolynomial x2CoeffPoly = varPoly.getCoefficientPoly(x2);

        SimplePolyConstraint spc1;
        final Set<SimplePolyConstraint> result = new LinkedHashSet<SimplePolyConstraint>(2);

        // x_1 and x_2 must have the same coefficient (in all cases!)
        spc1 = new SimplePolyConstraint(x1CoeffPoly.minus(x2CoeffPoly),
                ConstraintType.EQ);
        result.add(spc1);

        final int degree = Interpretation.computeDegreeOfBinaryInterpretation(varPoly);

        switch (degree) {
        case LINEAR :
        case SIMPLE :
        case SIMPLE_MIXED : {
            // nothing to do here
            break;
        }
        case 2 : {
            final Map<String, Integer> x1sqMap = new LinkedHashMap<String, Integer>(1);
            x1sqMap.put(x1, 2);
            final IndefinitePart x1sq = IndefinitePart.create(x1sqMap);
            final SimplePolynomial x1sqCoeff = varPoly.getCoefficientPoly(x1sq);
            final Map<String, Integer> x2sqMap = new LinkedHashMap<String, Integer>(1);
            x2sqMap.put(x2, 2);
            final IndefinitePart x2sq = IndefinitePart.create(x2sqMap);
            final SimplePolynomial x2sqCoeff = varPoly.getCoefficientPoly(x2sq);
            SimplePolyConstraint spc2;
            spc2 = new SimplePolyConstraint(x1sqCoeff.minus(x2sqCoeff),
                    ConstraintType.EQ);
            result.add(spc2);
            break;
        }
        default :
            throw new UnsupportedOperationException("cannot get C SPCs for degree " + degree + " (yet)");
        }

        return result;
    }

    private static int computeDegreeOfBinaryInterpretation(final VarPolynomial varPoly) {
        switch (varPoly.numberOfAddends()) {
        case 3 : // ax + by + c
            return Interpretation.LINEAR;
        case 4 : // ax + by + c + dxy
            return Interpretation.SIMPLE; // equiv to SIMPLE_MIXED (in binary case)
        case 6 : // ax + by + c + dxy + ex^2 + fy^2
            return 2;
        default :
            // TODO
            throw new RuntimeException("Cannot cope with " + varPoly.numberOfAddends() + " (yet)!");
        }
    }

    /**
     * Performs the actual generation of a generic polynomial interpretation
     * for the FunctionSymbol symbol.
     *
     * @param symbol we want its generic polynomial interpretation
     * @param degree the degree of the resulting generic polynomial if > 0,
     *  or SIMPLE, SIMPLE_MIXED or INDIVIDUAL
     * @return the resulting polynomial interpretation
     */
    public VarPolynomial getPolynomialFromFunction(final FunctionSymbol symbol,
            final int degree, final Abortion aborter) throws AbortionException {
        final int arity = symbol.getArity();

        final VarPolynomial[] variables = new VarPolynomial[arity];
        for (int i = 0; i < arity; ++i) {
            variables[i] = VarPolynomial.createVariable(Interpretation.VARIABLE_PREFIX + (i + 1));
        }

        VarPolynomial sum; // the result

        if (degree == Interpretation.LINEAR) {
            String coeff = this.getNextCoeff();
            VarPolynomial inter = VarPolynomial.createCoefficient(coeff);

            for (int i = 0; i<arity; i++) {
                coeff = this.getNextCoeff();
                final VarPolynomial c_i = VarPolynomial.createCoefficient(coeff);
                inter = inter.plus(c_i.times(variables[i]));
            }
            return inter;

        }

        if ((degree == Interpretation.SIMPLE) || ((degree == Interpretation.SIMPLE_MIXED) && (symbol.getArity() != 1))) {
            final Set<String> xs = new LinkedHashSet<String>();
            for (int i = 1; i <= arity; i++) {
                xs.add(Interpretation.VARIABLE_PREFIX + i);
            }

            PowerSet<String> variableSets;
            variableSets = new PowerSet<String>(ImmutableCreator.create(xs), this.maxSimpleDegree, false);

            sum = VarPolynomial.ZERO;

            for (final Set<String> vars : variableSets) {
                SimplePolynomial factor;
                factor = SimplePolynomial.create(this.getNextCoeff());
                final VarPolynomial addend = VarPolynomial.createProduct(vars, factor);
                sum = sum.plus(addend);
            }
        } else if (degree == Interpretation.SIMPLE_MIXED) {

            sum = VarPolynomial.createCoefficient(this.getNextCoeff());

            VarPolynomial coefficient = VarPolynomial.createCoefficient(this.getNextCoeff());
            sum = sum.plus(coefficient.times(variables[0]));

            if(!this.multilinear) {
                coefficient = VarPolynomial.createCoefficient(this.getNextCoeff());
                sum = sum.plus(coefficient.times(variables[0].power(2, aborter)));
            }
        } else {

            final Set<VarPolynomial> xs = new LinkedHashSet<VarPolynomial>(arity);
            for (int i=0; i<arity; i++) {
                xs.add(variables[i]);
            }

            sum = VarPolynomial.ZERO;

            for (final MultiSet<VarPolynomial> someXs : PowerMultiSet.createDestructively(xs, degree, false)) {
                boolean ignore = false;
                VarPolynomial prod = VarPolynomial.createCoefficient(this.getNextCoeff());
                for (final Entry<VarPolynomial,Integer> x : someXs.entrySet()) {
                    if(this.multilinear && x.getValue() > 1) {
                        ignore = true;
                    }
                    final VarPolynomial xPow = x.getKey().power(x.getValue(), aborter);
                    prod = prod.times(xPow);

                }
                if (!ignore) {
                    sum = sum.plus(prod);
                }

            }

        }

        return sum;
    }

    /**
     * Interprets a term t with a VarPolynomial, built up using
     * the polynomial interpretations of its function symbols.
     *
     * @param t the term to be interpreted
     * @return the polynomial which correspons to t in this
     */
    public VarPolynomial interpretTerm(final TRSTerm t, final Abortion aborter) throws AbortionException  {
        if (Globals.useAssertions) {
            assert ((t instanceof TRSFunctionApplication) ||
                    (t instanceof TRSVariable));
            // if other terms should ever be created, the below code
            // needs to be checked
        }

        VarPolynomial result;
        /*
        // have we already seen t?
        if (this.cache != null) {
            result = this.cache.get(t);
            if (result != null) {
                return result;
            }
        }
        */
        // apparently t has not been interpreted by this yet (or the
        // cached value has been cleared away).
        if (t.isVariable()) { // easy: Variable
            result = VarPolynomial.createVariable(((TRSVariable) t).getName());
        } else { // FunctionApplication
            // compute the interpretations of the arguments of t ...
            final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
            if (args.isEmpty()) { // fApp is a constant
                return this.pol.get(fApp.getRootSymbol());
            }
            Map<String, VarPolynomial> substitution;
            // x_j |-> poly interpretation of t|_j
            final int size = args.size();
            substitution = new LinkedHashMap<String, VarPolynomial>(size);
            for (int i = 0; i < size; ++i) {
                aborter.checkAbortion();
                final String argVar = Interpretation.VARIABLE_PREFIX + (i+1);
                final VarPolynomial argPoly = this.interpretTerm(args.get(i), aborter);
                substitution.put(argVar, argPoly);
            }
            // ... then get the interpretation of the root symbol
            final VarPolynomial temp = this.pol.get(fApp.getRootSymbol());
            // and plug the arg polys into the root poly
            aborter.checkAbortion();
            result = temp.substituteVariables(substitution, aborter);
        }
        /*
        if (this.cache != null) {
            this.cache.put(t, result);
        }
        */
        aborter.checkAbortion();
        return result;
    }

    /*
    public void clearCache() {
        if (this.cache != null) {
            this.cache.clear();
        }
    }
    */

    /**
     *
     * @return whether this interprets any FunctionSymbol
     */
    public boolean isEmpty() {
        return this.pol.isEmpty();
    }

    /**
     *
     * @param f we want its interpretation
     * @return the interpretation of f in this
     */
    public VarPolynomial get(final FunctionSymbol f) {
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
    public void put(final FunctionSymbol f, final VarPolynomial p) {
        if (Globals.useAssertions) {
            assert ! this.pol.containsKey(f);
            assert f != null;
            assert p != null;

            // commented, because the NonInfReductionPairProcessor needs
            // negative interpretations (e. g.for 'c').
            // assert p.allPositive();
            final Set<String> allowedVars = new LinkedHashSet<String>(f.getArity());
            final int n = f.getArity();
            for (int i = 1; i <= n; ++i) {
                allowedVars.add(Interpretation.VARIABLE_PREFIX + i);
            }
            assert allowedVars.containsAll(p.getVariables());
        }
        this.pol.put(f, p);
    }

    /**
     * Calculates a new Interpretation as the specialization of the current one
     * and sets all coefficients to value in given state. Those coefficients
     * that do not occur in the state will be set to defValue
     *
     * @param state docu-guess (fuhs): maps indefinite coefficients (!) to numbers
     *  by which they are supposed to be substituted
     * @param defValue the value for all those coefficients which do not occur
     */
    public Interpretation specialize(final Map<String, BigInteger> state, BigInteger defValue) {
        final Interpretation specialization = new Interpretation();
        if (defValue.signum() < 0) {
            defValue = BigInteger.ZERO;
        }
        for (final Entry<FunctionSymbol, VarPolynomial> entry : this.pol.entrySet()) {
            VarPolynomial polynomial = entry.getValue();
            polynomial = polynomial.specialize(state);
            // replace remaining coefficients by default Value
            polynomial = polynomial.setAllIndefiniteCoeffsTo(defValue);
            specialization.pol.put(entry.getKey(), polynomial);
        }
        return specialization;
    }

    /**
     * Exports the mapping from function symbols to polynomials with variables.
     *
     * @param eu the export util
     * @return the exported version of the interpretation
     */
    @Override
    public String export(final Export_Util eu) {
        final StringBuilder result = new StringBuilder("Polynomial interpretation "+eu.cite(this.citation)+":\n");

        final int size = this.pol.size();
        final List<Object> rows = new ArrayList<Object>(size);

        Map<FunctionSymbol, VarPolynomial> sortedPol; // for ordered display
        sortedPol = new TreeMap<FunctionSymbol, VarPolynomial>(this.pol);
        for (final Map.Entry<FunctionSymbol, VarPolynomial> entry : sortedPol.entrySet()) {
            final StringBuilder line = new StringBuilder("POL(");
            final FunctionSymbol functionSymbol = entry.getKey();
            final int arity = functionSymbol.getArity();

            final StringBuilder functionWithVars = new StringBuilder(functionSymbol.export(eu));
            if (arity > 0) {
                functionWithVars.append("(");
                for (int i = 1; i <= arity; ++i) {
                    StringBuilder varBuf;
                    final String var = Interpretation.VARIABLE_PREFIX + i;
                    final String[] split = var.split("_", 2);
                    varBuf = new StringBuilder(split[0]);
                    if (split.length > 1) {
                        varBuf.append(eu.sub(split[1]));
                    }
                    functionWithVars.append(varBuf);
                    if (i < arity) {
                        functionWithVars.append(", ");
                    }
                }
                functionWithVars.append(")");
            }

            line.append(eu.bold(functionWithVars.toString()));
            line.append(") = ");
            line.append(entry.getValue().export(eu));

            // nasty hack for equidistant lines in HTML (and hence the GUI)
            if (eu instanceof HTML_Util) {
                line.append("<sup>&nbsp;</sup> <sub>&nbsp;</sub>");
            }
            rows.add(eu.wrapAsRaw(line.toString()));
        }

        result.append(eu.set(rows, Export_Util.RULES));
        return result.toString();
    }



    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }


    /**
     * computes the extended AFS corresponding to this interpretation.
     * Requires that this is a concrete interpretation (without unchosen coefficients)
     * @return
     */
    public ExtendedAfs getExtendedAfs() {
        final Map<FunctionSymbol, QActiveCondition.Dependence[]> extAfs =
            new LinkedHashMap<FunctionSymbol, QActiveCondition.Dependence[]>(this.pol.size());

        for (final Map.Entry<FunctionSymbol, VarPolynomial> fPol : this.pol.entrySet()) {
            final FunctionSymbol f = fPol.getKey();
            final VarPolynomial inter = fPol.getValue();
            final int n = f.getArity();
            final Dependence[] deps = new Dependence[n];
            for (int i=0; i<n; i++) {
                final String var = Interpretation.VARIABLE_PREFIX + (i+1);
                boolean normal = false;
                boolean reverse = false;
                for (final SimplePolynomial sp : inter.getListOfCoefficientPolys(var)) {
                    assert(sp.isConstant());
                    switch (sp.getNumericalAddend().compareTo(BigInteger.ZERO)) {
                        case -1:
                            reverse = true;
                            break;
                        case 1:
                            normal = true;
                            break;
                        default:
                            throw new RuntimeException("Who puts zeros into coefficients?");
                    }
                }

                deps[i] = normal ? (reverse ? Dependence.Wild : Dependence.Incr) : (reverse ? Dependence.Decr : Dependence.None);
            }

            extAfs.put(f, deps);
        }

        return new QActiveCondition.ExtendedAfs() {

            @Override
            public Dependence filterPosition(final FunctionSymbol f, final int i) {
                return extAfs.get(f)[i];
            }

        };
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.POLO.createElement(doc);
        final Element degreeTag = XMLTag.DEGREE.createElement(doc);
        final Element degree = XMLTag.createInteger(doc, this.getDegree() + "");
        degreeTag.appendChild(degree);
        e.appendChild(degreeTag);
        for (final Map.Entry<FunctionSymbol, VarPolynomial> entry : this.pol.entrySet()) {
            final Element poloInter = XMLTag.POLO_INTERPRETATION.createElement(doc);
            poloInter.appendChild(entry.getKey().toDOM(doc, xmlMetaData));
            poloInter.appendChild(entry.getValue().toDOM(doc, xmlMetaData));
            e.appendChild(poloInter);
        }
        return e;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element domain = CPFTag.DOMAIN.create(doc, CPFTag.NATURALS.create(doc));
        final Element degree = CPFTag.DEGREE.create(doc,
                doc.createTextNode("" + this.getDegree()));
        final Element type = CPFTag.TYPE.create(doc,
                CPFTag.POLYNOMIAL.create(doc, domain, degree));
        final Element interpretation = CPFTag.INTERPRETATION.create(doc, type);
        for (final Map.Entry<FunctionSymbol, VarPolynomial> entry : this.pol.entrySet()) {
            final FunctionSymbol fSym = entry.getKey();
            final Element arity = CPFTag.ARITY.create(doc,
                    doc.createTextNode("" + fSym.getArity()));
            final Element interpret = CPFTag.INTERPRET.create(doc,
                    fSym.toCPF(doc, xmlMetaData),
                    arity,
                    entry.getValue().toCPF(doc, xmlMetaData));
            interpretation.appendChild(interpret);
        }
        return CPFTag.ORDERING_CONSTRAINT_PROOF.create(doc,
                CPFTag.RED_PAIR.create(doc,
                        interpretation));
    }

    public Citation getCitation() {
        return this.citation;
    }

    public void setCitation(final Citation citation) {
        this.citation = citation;
    }

    public void setLinearMonotone(final boolean linearMonotone) {
        this.linearMonotone = linearMonotone;
    }

    public void setMultilinear(final boolean multilinear) {
        this.multilinear = multilinear;
    }

	

}
