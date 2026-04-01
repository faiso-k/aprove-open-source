package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.LinearRelation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.Locations.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Error path indicating a cycle that does not satify the current ranking function.
 * @author marinag, cryingshadow
 */
public class ErrorPath implements Exportable {

    private static Set<SimplePolyConstraint> filter(final Set<SimplePolyConstraint> bound) {
        final Set<SimplePolyConstraint> toRemove = new HashSet<>();
        for (SimplePolyConstraint q : bound) {
            for (SimplePolyConstraint p : bound) {
                if (
                    !(
                        new SimplePolyConstraint(p.getPolynomial().minus(q.getPolynomial()), ConstraintType.GE)
                    ).isSatisfiable()
                ) {
                    toRemove.add(q);
                    break;
                }
            }
        }
        final Set<SimplePolyConstraint> filtered = new HashSet<>(bound);
        filtered.removeAll(toRemove);
        return filtered;
    }

    final Location cutPoint;

    final List<Edge<LinearTransitionPair, LocationID>> cycle;

    final Set<Node<LocationID>> cycleNodes;

    final Location errorLocation;

    final List<Edge<LinearTransitionPair, LocationID>> stem;

    private final LinearProgramGraph ug;

    /**
     * @param edges
     */
    public ErrorPath(LinearProgramGraph ug, List<Edge<LinearTransitionPair, LocationID>> edges) {
        this.errorLocation = (Location) edges.get(edges.size() - 1).getEndNode();
        this.cutPoint = (Location) edges.get(edges.size() - 1).getStartNode();
        this.cycle = new LinkedList<>();
        this.stem = new LinkedList<>();
        this.cycleNodes = new HashSet<>();
        this.ug = ug;
        boolean isStem = true;
        for (final Edge<LinearTransitionPair, LocationID> edge : edges) {
            final boolean skip =
                (((CoopLocation) edge.getEndNode()).getType().equals(CoopLocationType.CUTPOINT_DUPLICATE));
            isStem = isStem && !skip;
            if (skip) {
                continue;
            }
            if (isStem) {
                this.stem.add(edge);
            } else {
                if ((edge.getEndNode() instanceof AbortLocation)) {
                    continue;
                }
                this.cycleNodes.add(edge.getStartNode());
                this.cycleNodes.add(edge.getEndNode());
                this.cycle.add(edge);
            }
        }
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append("Stem:");
        res.append(eu.linebreak());
        res.append(eu.export(this.getStemTransitionPair()));
        res.append(eu.linebreak());
        res.append(eu.linebreak());
        res.append("Cycle:");
        res.append(eu.linebreak());
        res.append(eu.export(this.getTransitionPair()));
        res.append(eu.linebreak());
        return res.toString();
    }

    public LinearConstraintsSystem getBounded() {
        final Set<SimplePolyConstraint> constraints = this.getStemBounded().toSet();
        constraints.addAll(this.getCycleBound().getConstraints());
        return LinearConstraintsSystem.create(constraints);
    }

    public Location getCutPoint() {
        return this.cutPoint;
    }

    public List<Edge<LinearTransitionPair, LocationID>> getCycle() {
        return this.cycle;
    }

    public LinearConstraintsSystem getCycleBound() {
        PolyRelation relation = PolyRelation.create();
        final Set<SimplePolyConstraint> bound = new HashSet<>();
        for (Edge<LinearTransitionPair, LocationID> edge : this.cycle) {
            if (((CoopLocation) edge.getEndNode()).getType().equals(CoopLocationType.CUTPOINT_DUPLICATE)) {
                continue;
            }
            final LinearConstraintsSystem condition = relation.apply(edge.getObject().x);
            bound.addAll(condition.getConstraints());
            relation = PolyRelation.compose(relation, edge.getObject().y); // ((Location) edge.getStartNode()).getPolyRelation());
        }
        return LinearConstraintsSystem.create(ErrorPath.filter(bound)).toGeConstraintsSystem();
    }

    public Set<Node<LocationID>> getCycleNodes() {
        return this.cycleNodes;
    }

    public Location getErrorLocation() {
        return this.errorLocation;
    }

    public PolyRelation getRelation() {
        return this.getTransitionPair().y;
    }

    public List<Edge<LinearTransitionPair, LocationID>> getStem() {
        return this.stem;
    }

    public LinearConstraintsSystem getStemBounded() {
        final Set<SimplePolyConstraint> bound = new HashSet<>();
        PolyRelation relation = PolyRelation.create();
        final PolyRelation cycleR = this.getRelation();
        for (int i = this.stem.size() - 1; i > 0; i--) {
            final Edge<LinearTransitionPair, LocationID> edge = this.stem.get(i);
            relation = PolyRelation.compose(edge.getObject().y, relation);
            final ArrayList<SimplePolyConstraint> condition = relation.apply(edge.getObject().x).getConstraints();
            for (final SimplePolyConstraint c : condition) {
                final SimplePolynomial poly = c.getPolynomial();
                if (poly.isLinear() && (cycleR.compare(poly, ConstraintType.GE))) {
                    bound.add(c);
                }
            }
        }
        //        for (final Pair<String, SimplePolynomial> entry : relation.trim().getTransitions()) {
        //            if (entry.y == null) {
        //                continue;
        //            }
        //
        //            bound.add(new SimplePolyConstraint(entry.y.minus(SimplePolynomial.create(entry.x)), ConstraintType.EQ));
        //        }
        return LinearConstraintsSystem.create(ErrorPath.filter(bound)).toGeConstraintsSystem();
    }

    public PolyRelation getStemPolyRelation() {
        PolyRelation relation = PolyRelation.create();
        final Set<SimplePolyConstraint> bound = new HashSet<>();
        for (final Edge<LinearTransitionPair, LocationID> edge : this.stem) {
            if (!edge.getObject().x.equals(TermTools.TRUE)) {
                final LinearConstraintsSystem condition = relation.apply(edge.getObject().x);
                bound.addAll(condition.getConstraints());
            }
            final List<Pair<String, SimplePolynomial>> map = new ArrayList<>();
            relation = PolyRelation.compose(relation, edge.getObject().y);
            for (final Pair<String, SimplePolynomial> entry : relation.getTransitions()) {
                map.add(entry);
            }
            for (final String var : edge.getObject().x.getVariables()) {
                if (!relation.getVariablesNames().contains(var)) {
                    map.add(new Pair<String, SimplePolynomial>(var, null));
                }
            }
            relation = PolyRelation.createRelation(map);
        }
        return relation;
    }

    public LinearTransitionPair getStemTransitionPair() {
        final List<LinearTransitionPair> trans = new ArrayList<>();
        for (Edge<LinearTransitionPair, LocationID> e : this.getStem()) {
            trans.add(e.getObject());
        }
        return LinearTransitionPair.compose(trans);
    }

    public Set<SimplePolynomial> getToDecrease() {
        final Set<SimplePolynomial> polys = new HashSet<>();
        final LinearTransitionPair pair = this.getTransitionPair();
        for (final SimplePolyConstraint c : pair.x.getConstraints()) {
            polys.add(c.getPolynomial());
        }
        return polys;
    }

    public LinearTransitionPair getTransitionPair() {
        final List<LinearTransitionPair> trans = new ArrayList<>();
        for (Edge<LinearTransitionPair, LocationID> e : this.getCycle()) {
            if (((CoopLocation) e.getEndNode()).getType().equals(CoopLocationType.CUTPOINT_DUPLICATE)) {
                continue;
            }
            trans.add(e.getObject());
        }
        return LinearTransitionPair.compose(trans);
    }

}
