package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.Disjunctions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Utils.*;
import immutables.*;

/**
 * Nothing but a list of SimplePolyConstraints.
 * @author marinag
 */
public class PolyConstraintsSystem implements Exportable {

    /**
     * False.
     */
    public static PolyConstraintsSystem FALSE =
        new PolyConstraintsSystem(Arrays.asList(new SimplePolyConstraint(SimplePolynomial.ZERO, ConstraintType.GT)));

    /**
     * Empty constraints system.
     */
    public static PolyConstraintsSystem TRUE = PolyConstraintsSystem.create();

    /**
     * @param constraints constraints
     * @return a constraints system with the given constraints
     */
    public static PolyConstraintsSystem create(final Collection<SimplePolyConstraint> constraints) {
        final Set<SimplePolyConstraint> filtered = new HashSet<>();
        for (final SimplePolyConstraint c : constraints) {
            if (!c.isSatisfiable()) {
                return PolyConstraintsSystem.FALSE;
            } else if (!c.getPolynomial().isConstant()) {
                filtered.add(c);
            }
        }
        return new PolyConstraintsSystem(filtered);
    }

    /**
     * @param constraints constraints
     * @return a constraints system with the given constraints
     */
    public static PolyConstraintsSystem create(final SimplePolyConstraint... constraints) {
        for (final SimplePolyConstraint c : constraints) {
            if (!c.isSatisfiable()) {
                return PolyConstraintsSystem.FALSE;
            }
        }
        return PolyConstraintsSystem.create(Arrays.asList(constraints));
    }

    /**
     * @param constraint - constraint
     * @return List of constraints corresponding to negation of the constraint
     */
    public static ArrayList<SimplePolyConstraint> getNegated(final SimplePolyConstraint constraint) {
        final ArrayList<SimplePolyConstraint> result = new ArrayList<>();
        final SimplePolynomial poly = constraint.getPolynomial();
        if (constraint.getType().equals(ConstraintType.EQ)) {
            result.add(new SimplePolyConstraint(poly, ConstraintType.GT));
        }
        result.add(new SimplePolyConstraint(poly.times(BigInteger.ONE.negate()), ConstraintType.GT));
        return result;
    }

    public static HashSet<String> getVariables(final SimplePolynomial poly) {
        final HashSet<String> result = new HashSet<>();
        if (poly == null) {
            return result;
        }
        for (final IndefinitePart indef : poly.getSimpleMonomials().keySet()) {
            for (final String var : indef.getExponents().keySet()) {
                result.add(var);
            }
        }
        return result;
    }

    /**
     * @param a first constraints system
     * @param b second constraints system
     * @return a new constrains system containing the constraints of both the first and the second system
     */
    public static PolyConstraintsSystem merge(final PolyConstraintsSystem a, final PolyConstraintsSystem b) {
        final ArrayList<SimplePolyConstraint> constraints = a.getConstraints();
        constraints.addAll(b.constraints);
        return PolyConstraintsSystem.create(constraints);
    }

    /**
     * @param constraint polynomial constraint
     * @return constraints system corresponding to the negation of the given constraint
     */
    public static List<SimplePolyConstraint> negate(final SimplePolyConstraint constraint) {
        if (constraint.getType().equals(ConstraintType.GE)) {
            return Arrays.asList(new SimplePolyConstraint(
                constraint.getPolynomial().negate(),
                ConstraintType.GT));
        } else {
            return
                Arrays.asList(
                    new SimplePolyConstraint(constraint.getPolynomial(), ConstraintType.GT),
                    new SimplePolyConstraint(constraint.getPolynomial().negate(), ConstraintType.GT)
                );
        }
    }

    /**
     * @param constraint
     * @return
     */
    private static TRSTerm toTerm(final SimplePolyConstraint constraint) {
        switch (constraint.getType()) {
        case EQ:
            return ToolBox.buildEq(constraint.getPolynomial().toTerm(), ToolBox.buildInt(BigInteger.ZERO));
        case GT:
            return ToolBox.buildGt(constraint.getPolynomial().toTerm(), ToolBox.buildInt(BigInteger.ZERO));
        case GE:
            return ToolBox.buildGe(constraint.getPolynomial().toTerm(), ToolBox.buildInt(BigInteger.ZERO));
        default:
            throw new RuntimeException("invalid constraint type");
        }
    }

    /**
     * Constraints list.
     */
    protected ImmutableArrayList<SimplePolyConstraint> constraints;

    /**
     * Creates a constraints system with the given constraints
     * @param constraints constraints
     */
    protected PolyConstraintsSystem(final Collection<SimplePolyConstraint> constraints) {
        this.constraints = ImmutableCreator.create(new ArrayList<>(new HashSet<>(constraints)));
    }

    /**
     * Add all constraints in c to system
     * @param c collection of constraints
     * @return a new constraints system that contains all of the constraints of this system together with the all of the constraints of c
     */
    public PolyConstraintsSystem addAllConstraints(final Collection<SimplePolyConstraint> c) {
        PolyConstraintsSystem result = this;
        for (final SimplePolyConstraint cons : c) {
            result = result.addConstraint(cons);
        }
        return result;
    }

    /**
     * @param c polynomial constraint
     * @return a new constraints system that contains all of the constraints of this system together with the given constraint c
     */
    public PolyConstraintsSystem addConstraint(final SimplePolyConstraint c) {
        if (c.getPolynomial().isZero()) {
            return this;
        }
        final ArrayList<SimplePolyConstraint> newConstraints = new ArrayList<>();
        newConstraints.addAll(this.constraints);
        newConstraints.add(c);
        return new PolyConstraintsSystem(newConstraints);
    }

    /**
     * @return true if the system is satisfiable, false otherwise
     */
    public boolean constraitsSat() {
        for (final SimplePolyConstraint constraint : this.constraints) {
            if (!constraint.isSatisfiable()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @param sys constraints system
     * @return true if all of the constraints of sys are contained in this system
     */
    public boolean contains(final PolyConstraintsSystem sys) {
        return this.constraints.containsAll(sys.constraints);
    }

    /**
     * @param c - constraint
     * @return true if contains, false otherwise
     */
    public boolean contains(final SimplePolyConstraint c) {
        return this.constraints.contains(c);
    }

    @Override
    public boolean equals(final Object obj) {
        if (obj == null || !(obj instanceof PolyConstraintsSystem)) {
            return false;
        }
        final PolyConstraintsSystem system = (PolyConstraintsSystem) obj;
        if (this == system) {
            return true;
        }
        return this.toSet().equals(system.toSet());
    }

    @Override
    public String export(Export_Util eu) {
        return eu.set(this.constraints, Export_Util.RULES);
    }

    /**
     * @param index - constraint index
     * @return constraint at index
     */
    public SimplePolyConstraint get(final int index) {
        return this.constraints.get(index);
    }

    /**
     * @param id - indefinite part
     * @param constraint - constraint index
     * @return coefficient of id in corresponding constraint
     */
    public BigInteger getCoef(final IndefinitePart id, final int constraint) {
        final ImmutableMap<IndefinitePart, BigInteger> monomials =
            this.get(constraint).getPolynomial().getSimpleMonomials();
        if (!monomials.keySet().contains(id)) {
            return BigInteger.ZERO;
        }
        return monomials.get(id);
    }

    /**
     * @param id - indefinite part
     * @return coefficients vector of id
     */
    public ArrayList<BigInteger> getCoefs(final IndefinitePart id) {
        final int length = this.size();
        final ArrayList<BigInteger> result = new ArrayList<>(length);
        for (int i = 0; i < length; i++) {
            result.add(this.getCoef(id, i));
        }
        return result;
    }

    /**
     * @return Constraints list
     */
    public ArrayList<SimplePolyConstraint> getConstraints() {
        return new ArrayList<>(this.constraints);
    }

    public List<Formula<SMTLIBTheoryAtom>> getFormulas() {
        final LinkedList<Formula<SMTLIBTheoryAtom>> formulas = new LinkedList<>();
        final FormulaFactory<SMTLIBTheoryAtom> factory = new FullSharingFactory<SMTLIBTheoryAtom>();
        for (final SimplePolyConstraint c : this.toSet()) {
            formulas.add(factory.buildTheoryAtom(c.toSMTLIB()));
        }
        return formulas;
    }

    /**
     * @return Set of indefinite parts
     */
    public HashSet<String> getIdefinities() {
        final HashSet<String> ids = new HashSet<>();
        for (final SimplePolyConstraint c : this.constraints) {
            ids.addAll(c.getIndefinites());
        }
        return ids;
    }

    /**
     * @return constraints indefinite parts
     */
    public HashSet<IndefinitePart> getIndefiniteParts() {
        final HashSet<IndefinitePart> indef = new HashSet<>();
        for (final SimplePolyConstraint c : this.constraints) {
            indef.addAll(c.getPolynomial().getSimpleMonomials().keySet());
        }
        return indef;
    }

    /**
     * @return the linear constraints only
     */
    public LinearConstraintsSystem getLinearPart() {
        final HashSet<SimplePolyConstraint> constraints = new HashSet<>();
        for (final SimplePolyConstraint c : this.getConstraints()) {
            if (c.getPolynomial().isLinear()) {
                constraints.add(c);
            }
        }
        return LinearConstraintsSystem.create(constraints);
    }

    public List<SimplePolynomial> getPolynomials() {
        final List<SimplePolynomial> polys = new ArrayList<>();
        for (final SimplePolyConstraint c : this.constraints) {
            polys.add(c.getPolynomial());
        }
        return polys;
    }

    public Set<String> getVariables() {
        final Set<String> variables = new HashSet<>();
        for (final SimplePolyConstraint c : this.getConstraints()) {
            variables.addAll(c.getPolynomial().getVariables());
        }
        return variables;
    }

    @Override
    public int hashCode() {
        return this.toSet().hashCode();
    }

    /**
     * @return true is constraints no constrains, false otherwise
     */
    public boolean isEmpty() {
        return this.constraints.isEmpty();
    }

    /**
     * @return true if represents a FALSE system, false otherwise
     */
    public boolean isFalse() {
        return this.contains(PolyConstraintsSystem.FALSE);
    }


    /**
     * @return true if all contained constraints are linear, false otherwise
     */
    public boolean isLinear() {
        for (final SimplePolyConstraint cons : this.constraints) {
            if (!cons.getPolynomial().isLinear()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return  true if represents a TRUE system (=no constraints), false otherwise
     */
    public boolean isTrue() {
        return this.equals(PolyConstraintsSystem.TRUE);
    }

    /**
     * @param id - indefinite part
     * @return true if all coefficients of id are zero, false otherwise
     */
    public boolean isZeroCoef(final IndefinitePart id) {
        if (this.constraints.isEmpty()) {
            return true;
        }
        final HashSet<BigInteger> coefs_a = new HashSet<>(this.getCoefs(id));
        return (coefs_a.size() == 1 && coefs_a.contains(BigInteger.ZERO));
    }

    /**
     * Merge with constraints of c
     * @param c - constraints system
     * @return
     */
    public PolyConstraintsSystem merge(final PolyConstraintsSystem c)     {
        final HashSet<SimplePolyConstraint> constraints = new HashSet<>(this.constraints);
        constraints.addAll(c.constraints);
        return PolyConstraintsSystem.create(constraints);
    }

    /**
     * @param consSys constraints system
     * @return negation of consSys
     */
    public PolyDisjunction negate() {
        if (this.isTrue()) {
            return PolyDisjunction.FALSE;
        }
        if (this.isFalse()) {
            return PolyDisjunction.TRUE;
        }
        PolyDisjunction result = PolyDisjunction.FALSE;
        for (final SimplePolyConstraint cons : this.getConstraints()) {
            for (final SimplePolyConstraint c : PolyConstraintsSystem.negate(cons)) {
                result = result.addSystem(PolyConstraintsSystem.create(c));
            }
        }
        return result;
    }

    /**
     * Remove constraints of c
     * @param c - collection of constraints
     */
    public PolyConstraintsSystem remove(final Collection<SimplePolyConstraint> c) {
        final HashSet<SimplePolyConstraint> constraints = this.toSet();
        for (final SimplePolyConstraint cons : c) {
            while (constraints.remove(cons)) {
            }
        }
        return PolyConstraintsSystem.create(constraints);
    }

    /**
     * @param map renaming map
     * @return rename all variables according to the given map, those who are not specified in it remain the same
     */
    public PolyConstraintsSystem rename(final Map<String, String> map) {
        PolyConstraintsSystem result = PolyConstraintsSystem.TRUE;
        for (final SimplePolyConstraint cons : this.constraints) {
            result = result.addConstraint(cons.replace(map));
        }
        return result;
    }

    public PolyConstraintsSystem restrictVariables(final Set<String> variables) {
        final Set<SimplePolyConstraint> constraints = new HashSet<>();
        for (final SimplePolyConstraint c : this.toSet()) {
            if (variables.containsAll(c.getPolynomial().getVariables())) {
                constraints.add(c);
            }
        }
        return PolyConstraintsSystem.create(constraints);
    }

    /**
     * @return number of constraints
     */
    public int size() {
        return this.constraints.size();
    }

    public PolyConstraintsSystem toGeConstraintsSystem() {
        final ArrayList<SimplePolyConstraint> newConstraints = new ArrayList<>();
        for (final SimplePolyConstraint c : this.constraints) {
            if (c.getType().equals(ConstraintType.EQ)) {
                final SimplePolynomial poly = c.getPolynomial();
                newConstraints.add(new SimplePolyConstraint(poly, ConstraintType.GE));
                newConstraints.add(new SimplePolyConstraint(poly.negate(), ConstraintType.GE));
            } else {
                newConstraints.add(c);
            }
        }
        return PolyConstraintsSystem.create(newConstraints);
    }

    public HashSet<SimplePolyConstraint> toSet() {
        return new HashSet<>(this.constraints);
    }

    /**
     * @param scope variable scope
     * @return corresponding Expression<SBool>
     */
    public SMTExpression<SBool> toSMTExp(final VariableScope scope) {
        if (this.isTrue()) {
            return Core.True;
        }
        if (this.isFalse()) {
            return Core.False;
        }
        final List<SMTExpression<SBool>> expressions = new LinkedList<>();
        for (final SimplePolyConstraint constraint : this.constraints) {
            expressions.add(constraint.toSMTExp(scope));
        }
        return Core.and(expressions);
    }

    @Override
    public String toString() {
        if (this.isEmpty()) {
            return "True";
        }
        if (this.isFalse()) {
            return "False";
        }
        final StringBuilder builder = new StringBuilder();
        final Iterator<SimplePolyConstraint> iterator = this.constraints.iterator();
        while (iterator.hasNext()) {
            builder.append(iterator.next());
            if (iterator.hasNext()) {
                builder.append(" & ");
            }
        }
        return builder.toString();
    }

    public TRSTerm toTerm() {
        if (this.isTrue()) {
            return ToolBox.buildTrue();
        }
        if (this.isFalse()) {
            return ToolBox.buildFalse();
        }
        final Set<TRSTerm> terms = new HashSet<>();
        final Set<SimplePolynomial> equalities = new HashSet<>();
        for (final SimplePolyConstraint cons : this.toSet()) {
            final SimplePolynomial poly = cons.getPolynomial().negate();
            if (equalities.contains(poly)) {
                continue;
            }
            if (this.constraints.contains(new SimplePolyConstraint(poly, ConstraintType.GE))) {
                equalities.add(cons.getPolynomial());
            }
        }
        for (final SimplePolyConstraint cons : this.toSet()) {
            final SimplePolynomial poly = cons.getPolynomial();
            if (equalities.contains(poly) || equalities.contains(poly.negate())) {
                continue;
            }
            terms.add(PolyConstraintsSystem.toTerm(cons));
        }
        for (final SimplePolynomial eq : equalities) {
            terms.add(PolyConstraintsSystem.toTerm(new SimplePolyConstraint(eq, ConstraintType.EQ)));
        }
        return ToolBox.buildAnd(terms);
    }

    /**
     * @param valueMap
     * @return
     */
    public Boolean tryEvaluate(final Map<String, BigInteger> valueMap) {
        boolean requireFalse = false;
        for (final SimplePolyConstraint c : this.constraints) {
            final Boolean value = c.tryEvaluate(valueMap);
            if (value == null) {
                requireFalse = true;
            } else {
                if (!value) {
                    return false;
                }
            }
        }
        return requireFalse ? null : true;
    }

}
