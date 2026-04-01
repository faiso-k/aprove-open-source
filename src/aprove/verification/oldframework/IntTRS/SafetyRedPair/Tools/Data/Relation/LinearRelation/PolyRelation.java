package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.LinearRelation;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.TermRelation.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author marinag
 * Polynomial relation
 */
public class PolyRelation extends GenericRelation<SimplePolynomial, PolyNextValue> {


    protected PolyRelation(final List<Pair<String, PolyNextValue>> transVec) {
        super(transVec);
    }

    public static PolyRelation createRelation(final List<Pair<String, SimplePolynomial>> map) {
        final List<Pair<String, PolyNextValue>> relMap = new ArrayList<>();

        for (final Pair<String, SimplePolynomial> entry : map) {
            relMap.add(new Pair<>(entry.x, new PolyNextValue(entry.y)));
        }

        return PolyRelation.create(relMap);
    }

    public static PolyRelation create(final List<Pair<String, PolyNextValue>> relMap) {
        return new PolyRelation(relMap);
    }

    public static PolyRelation createIdentity(final List<String> vars) {
        final List<Pair<String, SimplePolynomial>> relMap = new ArrayList<>();

        for (final String var : vars) {
            relMap.add(new Pair<>(var, SimplePolynomial.create(var)));
        }

        return PolyRelation.createRelation(relMap);
    }

    public static PolyRelation create() {
        return PolyRelation.create(new ArrayList<Pair<String, PolyNextValue>>());
    }

    /**
     * @param poly simple polynomial
     * @param type constraint type
     * @return true if the difference in the given polynomial under this relation always satisfies the given constraint type.
     */
    public boolean compare(final SimplePolynomial poly, final ConstraintType type) {
        final SimplePolynomial post = this.apply(new PolyNextValue(poly));

        if (post == null) {
            return false;
        }

        final SimplePolynomial diff = post.minus(poly);

        switch (type) {
        case EQ:
            return !(new SimplePolyConstraint(diff, ConstraintType.GT).isSatisfiable())
                && !(new SimplePolyConstraint(diff.negate(), ConstraintType.GT).isSatisfiable());
        case GE:
            return !(new SimplePolyConstraint(diff, ConstraintType.GT).isSatisfiable());
        case GT:
            return !(new SimplePolyConstraint(diff, ConstraintType.GE).isSatisfiable());
        default:
            return false;
        }
    }

    /**
     * @param relA first relation
     * @param relB second relation
     * @return a composition relation of the first and the second relation
     */
    public static PolyRelation compose(final PolyRelation relA, final PolyRelation relB) {
        if (relA.isIdentity()) {
            return relB;
        }

        if (relB.isIdentity()) {
            return relA;
        }

        final List<Pair<String, PolyNextValue>> transitions = new ArrayList<>();

        for (final Pair<String, PolyNextValue> b : relB.getTransVector()) {
            transitions.add(new Pair<>(b.getKey(), new PolyNextValue(relA.apply(b.getValue()))));
        }

        for (final Pair<String, PolyNextValue> a : relA.getTransVector()) {
            if (!relB.getVariablesNames().contains(a.getKey())) {
                transitions.add(new Pair<>(a.getKey(), a.getValue()));
            }
        }

        return PolyRelation.create(transitions);
    }


    /**
     * @param relations relations
     * @return composition of the given relations
     */
    public static PolyRelation compose(final Iterable<PolyRelation> relations) {
        PolyRelation result = PolyRelation.create();

        for (final PolyRelation current : relations) {
            result = PolyRelation.compose(result, current);
        }

        return result;
    }

    private PolyRelation extendToNdt() {
        final Set<String> ndtVars = this.getReferedVariableNames();
        ndtVars.removeAll(this.getVariablesNames());

        if (ndtVars.isEmpty()) {
            return this;
        }

        final ArrayList<Pair<String, SimplePolynomial>> list = new ArrayList<>();
        list.addAll(this.getTransitions());

        for (final String v : ndtVars) {
            list.add(new Pair<>(v, SimplePolynomial.create(PolyRelation.ng.getFreshName("ndt", false))));
        }

        return PolyRelation.createRelation(list);
    }

    public LinearConstraintsSystem apply(final LinearConstraintsSystem conSys) {
        //final PolyRelation extended = this.extendToNdt();

        final Set<SimplePolyConstraint> constraints = new HashSet<>();


        for (final SimplePolyConstraint c : conSys.getConstraints()) {
            final SimplePolyConstraint aCons = this.apply(c);

            if (aCons == null) {
                continue;
            }

            constraints.add(aCons);
        }

        return LinearConstraintsSystem.create(constraints);
    }

    public SimplePolyConstraint apply(final SimplePolyConstraint constraint) {
        final SimplePolynomial aPoly = this.apply(constraint.getPolynomial());

        if (aPoly == null) {
            return null;
        }

        return new SimplePolyConstraint(aPoly, constraint.getType());
    }

    public SimplePolynomial apply(final SimplePolynomial poly) {
        return super.apply(new PolyNextValue(poly));
    }

    public VarPolynomial apply(final VarPolynomial vp) {
        final Map<IndefinitePart, SimplePolynomial> mon = new HashMap<>();

        for (final Entry<IndefinitePart, SimplePolynomial> p : vp.getVarMonomials().entrySet()) {
            final SimplePolynomial poly = this.apply(p.getValue());
            if (poly.isZero()) {
                continue;
            }
            mon.put(p.getKey(), poly);
        }

        return VarPolynomial.create(ImmutableCreator.create(mon));
    }

    public PolyRelation remove(final Set<String> variables) {
        final List<Pair<String, PolyNextValue>> newT = new ArrayList<>();
        for (final Pair<String, PolyNextValue> entry : this.getTransVector()) {
            if (variables.contains(entry.getKey())) {
                continue;
            }
            newT.add(entry);
        }
        return PolyRelation.create(newT);
    }

    public PolyRelation restrict(final Set<String> variables) {
        final List<Pair<String, PolyNextValue>> newT = new ArrayList<>();
        for (final Pair<String, PolyNextValue> entry : this.getTransVector()) {
            if (variables.contains(entry.getKey())) {
                newT.add(entry);
            }
        }
        return PolyRelation.create(newT);
    }

    public PolyRelation trim() {
        final List<Pair<String, PolyNextValue>> newT = new ArrayList<>();
        for (final Pair<String, PolyNextValue> entry : this.getTransVector()) {
            if (entry.getValue() == null
                || !SimplePolynomial.create(entry.getKey()).equals(entry.getValue().getValue()))
            {
                newT.add(entry);
            }
        }
        return PolyRelation.create(newT);
    }

    public PolyRelation extend() {
        final List<Pair<String, SimplePolynomial>> newT = new ArrayList<>();
        final Set<String> allVars = new HashSet<>();

        for (final Pair<String, SimplePolynomial> entry : this.getTransitions()) {
            newT.add(entry);

            if (entry.getValue() != null) {
                allVars.addAll(entry.getValue().getVariables());
            }
        }

        allVars.removeAll(this.getVariablesNames());

        for (final String var : allVars) {
            newT
            .add(new Pair<String, SimplePolynomial>(var, SimplePolynomial.create(PolyRelation.ng.getFreshName("unknown", false))));
        }

        return PolyRelation.createRelation(newT);
    }

    @Override
    public String toString() {
        return this.trim().getTransitions().toString();
    }

    public SimplePolynomial apply(final String name) {
        return this.apply(SimplePolynomial.create(name));
    }

    public boolean unchanged(final String name) {
        return SimplePolynomial.create(name).equals(this.apply(name));
    }

    public TermRelation toTermRelation(final TRSSubstitution sigma) {
        final List<Pair<TRSVariable, TRSTerm>> tPairs = new ArrayList<>();

        final Set<TRSVariable> unDefFunVars = sigma.toMap().keySet();

        for (final Pair<String, SimplePolynomial> pair : this.getTransitions()) {
            final TRSVariable var = TRSTerm.createVariable(pair.x);

            if (unDefFunVars.contains(var)) {
                continue;
            }

            tPairs.add(new Pair<>(var, pair.y == null ? null : pair.y.toTerm().applySubstitution(sigma)));
        }

        return TermRelation.createRelation(tPairs);
    }

    public PolyRelation rename(final Map<String, String> renameMap) {
        final List<Pair<String, SimplePolynomial>> pairs = new ArrayList<>();

        for (final Pair<String, SimplePolynomial> pair : this.getTransitions()) {
            final String var = renameMap.containsKey(pair.x) ? renameMap.get(pair.x) : pair.x;
            pairs.add(new Pair<>(var, pair.y == null ? null : pair.y.replace(renameMap)));
        }

        return PolyRelation.createRelation(pairs);
    }

    public int getRank() {
        int rank = 0;

        for (final Pair<String, SimplePolynomial> p : this.getTransitions()) {
            if (!p.getValue().isConstant()) { //.isZero()) {
                rank++;
            }
        }
        return rank;
    }

    private static FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
}
