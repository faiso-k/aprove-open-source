package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Safety.Tree.Vertex;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.Disjunctions.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.LinearRelation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;


/**
 * Vertex of the unwinding tree
 * @author marinag
 */
public class Vertex extends BasicVertex {
    private boolean trueTrans = false;
    private boolean falseTrans = false;

    public Map<String, BigInteger> instancesValues = new HashMap<>();


    private ImmutableStack<SimplePolynomial> expStack;
    private ImmutableStack<Pair<Location, Location>> callStack;
    private LinearConstraintsSystem assumption = LinearConstraintsSystem.create();

    private Map<FunctionSymbol, Set<String>> fSymToVars = new HashMap<>();
    private Map<String, Pair<TRSFunctionApplication, List<String>>> varsToFApp = new HashMap<>();
    private final Map<String, Pair<TRSFunctionApplication, List<String>>> undefFunVars;

    public Map<FunctionSymbol, Set<String>> getFSymToVars() {
        return this.fSymToVars;
    }

    public Map<String, Pair<TRSFunctionApplication, List<String>>> getVarsToVars() {
        return this.varsToFApp;
    }

    /**
     * Create new instances of variables refering to undefined function applications, whose parametrers were changed by relation
     * @param relation - transition relation
     * @param father - father vertex
     */
    private void addUndefVariables(
        final PolyRelation relation,
        final Vertex father)
    {
        final Map<String, String> fullNames = this.getInstances();

        this.fSymToVars = father.fSymToVars;
        this.varsToFApp = father.varsToFApp;

        for (final Entry<String, Pair<TRSFunctionApplication, List<String>>> entry : new HashSet<>(
            this.undefFunVars.entrySet()))
        {
            final String var = entry.getKey();
            final String label = this.getStackSuffix();

            final String fullNameVar = fullNames.get(var + label);
            final FunctionSymbol fs = entry.getValue().x.getRootSymbol();

            if (!this.fSymToVars.containsKey(fs)) {
                this.fSymToVars.put(fs, new HashSet<String>());
            }
            if (relation.unchanged(var)) {
                continue;
            }
            final List<String> args = new ArrayList<>();
            for (final String arg : entry.getValue().y) {
                args.add(fullNames.containsKey(arg) ? fullNames.get(arg) : arg + label);
            }
            this.fSymToVars.get(fs).add(fullNameVar);
            this.varsToFApp.put(fullNameVar, new Pair<>(entry.getValue().x, args));
            this.undefFunVars.put(fullNameVar, new Pair<>(entry.getValue().x, args));
        }
    }


    public boolean isTrueTransition() {
        return this.trueTrans;
    }

    public boolean isFalseTransition() {
        return this.falseTrans;
    }

    private Map<String, SimplePolynomial> assignedPolys = new HashMap<>();
    private Stack<Map<String, String>> instances = new Stack<>();
    private Map<String, String> revInstances = new HashMap<>();
    private final int depth;

    /**
     * Create new root vertex corresponding to Location l
     * @param id - vertex id
     * @param l - corresponding Location
     * @param undefFVars - mapping of variables to corresponding undefined function applications
     */
    public Vertex(
        final int id,
        final Location l,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> undefFVars)
    {
        super(id, l);
        this.expStack = ImmutableCreator.create(new Stack<SimplePolynomial>());
        this.callStack = ImmutableCreator.create(new Stack<Pair<Location, Location>>());
        this.undefFunVars = undefFVars;
        this.instancesValues = new HashMap<>();
        this.depth = 0;
        this.instances.push(new HashMap<String, String>());
    }

    /**
     * Create new root vertex corresponding to Location l based on the state of Vertex v
     * @param id - vertex id
     * @param l - corresponding Location
     * @param v
     * @param undefFVars - mapping of variables to corresponding undefined function applications
     */
    public Vertex(
        final int id,
        final Location l,
        final Vertex v,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> undefFVars)
    {
        super(id, l);
        this.expStack = v.expStack;
        this.callStack = v.callStack;
        this.undefFunVars = undefFVars;
        this.depth = v.depth;
        this.instances = v.instances;
        this.assignedPolys = v.assignedPolys;
        this.revInstances = v.revInstances;
    }




    /**
     * Create child vertex by transition pair
     * @param id - vertex id
     * @param edge - creating edge
     * @param father - father Vertex
     * @param tp - transition pair
     */
    protected Vertex(
        final int id,
        final Edge<LinearTransitionPair, LocationID> edge,
        final Vertex father,
        final LinearTransitionPair tp)
    {
        super(id, edge);
        this.depth = father.depth + 1;

        this.revInstances.putAll(father.revInstances);
        this.assignedPolys.putAll(father.assignedPolys);
        this.instances = new Stack<>();

        final Iterator<Map<String, String>> iterator = father.instances.iterator();
        while (iterator.hasNext()) {
            this.instances.push(new HashMap<String, String>());
            this.instances.peek().putAll(iterator.next());
        }

        final Set<String> detVariables = new HashSet<>();
        for (final Pair<String, SimplePolynomial> entry : tp.y.getTransitions()) {
            if (entry.getValue() != null
                && entry.getValue().minus(SimplePolynomial.create(entry.getKey())).equals(SimplePolynomial.ZERO))
            {
                continue;
            }

            final String stackTag = entry.x;
            final String instance = stackTag + this.getDepthSuffix();
            this.getInstances().put(entry.x, instance);
            this.revInstances.put(instance, stackTag);
            detVariables.add(stackTag);
        }

        for (final String var : tp.x.getVariables()) {
            if (!detVariables.contains(var) && !var.contains("^")) {
                final String instance = var + this.getDepthSuffix();
                this.getInstances().put(var, instance);
                this.revInstances.put(instance, var);
            }
        }

        this.undefFunVars = father.undefFunVars;
        this.instancesValues = new HashMap<>(father.instancesValues);

        final List<Pair<String, SimplePolynomial>> transitions = new ArrayList<>();
        transitions.addAll(tp.y.getTransitions());

        final Location fatherLocation = father.getLocation();

        final Set<SimplePolyConstraint> equalities = new HashSet<>();

        if (fatherLocation instanceof PushLocation) {

            String var = ((PushLocation) fatherLocation).getPushedVariable() + father.getStackSuffix();

            var =
                father.instances.isEmpty() || !father.instances.peek().containsKey(var) ? var : father.instances
                    .peek()
                    .get(var);

            SimplePolynomial poly = SimplePolynomial.create(var);
            poly = this.getDeepestAssignment(SimplePolynomial.create(var).replace(father.getInstances()));

            this.expStack = father.expStack.doPush(poly);
        } else {
            this.expStack = father.expStack;
        }

        if (fatherLocation instanceof PopLocation) {
            final String stackTag =
                ((PopLocation) fatherLocation).getVariable() + this.getStackSuffix();
            final String instance = stackTag + this.getDepthSuffix();
            this.instances.peek().put(((PopLocation) fatherLocation).getVariable(), instance);
            this.revInstances.put(instance, stackTag);

            this.assignedPolys.put(instance, father.expStack.peek());
            equalities.add(new SimplePolyConstraint(
                SimplePolynomial.create(instance).minus(father.expStack.peek()),
                ConstraintType.EQ));

            if (father.expStack.peek().isConstant()) {
                this.instancesValues.put(instance, father.expStack.peek().getNumericalAddend());
            }

            this.expStack = father.expStack.doPop();
        }

        if (fatherLocation instanceof ReturnLocation) {
            this.instances.pop();
            this.callStack = father.callStack.doPop();
        } else if (fatherLocation instanceof CallLocation) {
            this.instances.push(new HashMap<String, String>());
            final Pair<Location, Location> pair =
                new Pair<>(this.getLocation(), ((CallLocation) fatherLocation).getReturnLocation());
                this.callStack = father.callStack.doPush(pair);
        } else {
            this.callStack = father.callStack;
        }

        for (final Pair<String, SimplePolynomial> entry : transitions) {
            if (entry.getValue() == null) {
                continue;
            }

            final SimplePolynomial poly = SimplePolynomial.create(entry.x).replace(this.getInstances());
            final SimplePolynomial vP = entry.getValue().replace(father.getInstances());

            if (poly.equals(vP)) {
                continue;
            }

            this.assignedPolys.put(poly.toString(), vP);
            equalities.add(new SimplePolyConstraint(vP.minus(poly), ConstraintType.EQ));
        }

        this.assumption = LinearConstraintsSystem.create(equalities);
        this.addUndefVariables(edge.getObject().y, father);
    }

    /**
     * @param poly simple polynomial
     * @return deepest possible evaluation of poly, used for values stack
     */
    private SimplePolynomial getDeepestAssignment(final SimplePolynomial poly) {
        if (poly.isConstant()) {
            return poly;
        }
        assert poly.isLinear();
        final Set<SimplePolynomial> polys = new HashSet<>();
        for (final Entry<IndefinitePart, BigInteger> entry : poly.getSimpleMonomials().entrySet()) {
            if (entry.getKey().isOne()) {
                polys.add(SimplePolynomial.create(entry.getKey(), entry.getValue()));
            } else {
                final String var = entry.getKey().toString();
                SimplePolynomial aPoly;

                if (!this.assignedPolys.containsKey(var)) {
                    aPoly = SimplePolynomial.create(var);
                } else {
                    final SimplePolynomial assigned = this.assignedPolys.get(var);

                    if (assigned == null) {
                        aPoly = SimplePolynomial.create(var);
                    } else {
                        aPoly = (this.getDeepestAssignment(assigned));
                    }
                }
                polys.add(aPoly.times(entry.getValue()));
            }
        }
        return SimplePolynomial.plus(polys);
    }

    /**
     * @return assumption condition of the incomming transition to this vertex
     */
    public LinearConstraintsSystem getAssumption() {
        return this.assumption;
    }

    /**
     * @return current (=at this vertex) variable instances fully tagged names
     */
    public Map<String, String> getInstances() {
        return this.instances.isEmpty() ? new HashMap<String, String>() : this.instances.peek();
    }

    /**
     * @param id - vertex id for child
     * @param edge - creating edge
     * @param tp - transition pair
     * @return created child vertex
     */
    public Vertex createChild(
        final int id,
        final Edge<LinearTransitionPair, LocationID> edge,
        final LinearTransitionPair tp)
    {
        assert (this.getLocation().equals(edge.getStartNode()));
        final Vertex child = new Vertex(id, edge, this, tp);

        final PolyConstraintsSystem cond = tp.x.rename(this.getInstances());

        Boolean transition;
        if (cond.isFalse()) {
            transition = false;
        } else if (cond.isTrue()) {
            transition = true;
        } else {
            final Map<String, BigInteger> values = new HashMap<>();

            for (final String var : cond.getVariables()) {
                final SimplePolynomial poly =
                    this.getDeepestAssignment(SimplePolynomial.create(var).replace(this.getInstances()));
                if (poly.isConstant()) {
                    values.put(var, poly.getNumericalAddend());
                }
            }

            transition = cond.tryEvaluate(values);
            if (transition != null) {
                child.trueTrans = transition;
                child.falseTrans = !transition;
            }
        }

        return child;
    }

    /**
     * @return call stack id, each call sequence gets its unique id for refernse
     */
    public Integer getStackDepthLabel() {
        if (!Vertex.PATH_STACK_ID.containsKey(this.callStack)) {
            Vertex.PATH_STACK_ID.put(this.callStack, Vertex.PATH_STACK_ID.keySet().size());
        }
        return Vertex.PATH_STACK_ID.get(this.callStack);
    }

    /**
     * @return current return location, on the top of the call stack. Returns null, if stack is empty.
     */
    public Location getReturnLocation() {
        if (this.callStack.isEmpty()) {
            return null;
        }

        return this.callStack.peek().y;
    }


    /**
     * Stranghten current formula by f (conjunction). If the resulting labeling turns to be UNSAT, the vertex is marked as infeasible.
     * @param disjunctionSolver - disjunction solver
     * @param f - labeling formula
     */
    public void strengthenLabeling(final DisjunctionSolver disjunctionSolver, final LinearDisjunction f)
    {
        this.getObject().setLabeling(disjunctionSolver.conjunction(this.getObject().getLabeling(), f));

        if (this.getObject().getLabeling().isEmpty()) {
            this.setInfeasible();
        }
    }

    /**
     * @return labeling formula
     */
    public LinearDisjunction getLabeling() {
        return this.getObject().getLabeling();
    }


    @Override
    public boolean equals(final Object obj) {
        if (obj == null || !(obj instanceof Vertex)) {
            return false;
        }

        return this.getId() == ((Vertex) obj).getId();
    }

    @Override
    public int hashCode() {
        return this.getId();
    }


    /**
     * Static vertices counter (used for unique id)
     */
    private static int vertexCounter = 0;


    @Override
    public String toString() {
        return "V" + this.getId() + "[" + this.getLocation() + "]";
    }

    public boolean equalStackTop(final Vertex v) {
        if (this.expStack.isEmpty()) {
            return v.expStack.isEmpty();
        } else {
            return !v.expStack.isEmpty() && this.expStack.peek().equals(v.expStack.peek());
        }
    }


    public boolean isFalseLabel() {
        return this.getLabeling().isEmpty();
    }

    public boolean isCoverCandidate() {
        return !(this.getLocation() instanceof ReturnLocation);
    }

    /**
     * set this vertex to be infeasible
     */
    public void setInfeasible() {
        this.getObject().setLabeling(LinearDisjunction.FALSE);
    }

    private static Map<Stack<Pair<Location, Location>>, Integer> PATH_STACK_ID = new HashMap<>();


    public SimplePolynomial getStackTop() {
        if (this.expStack.isEmpty()) {
            return SimplePolynomial.create("$empty");
        } else {
            return this.expStack.peek();
        }
    }

    /**
     * Variable instances delimiters, used for creating a full variable name of the form: var_{x}^{y},
     * where 'var' is the original variable names, 'x' is the call stack state id,
     * 'y' is the instance tag. If x=0, the no stack tag is added. Same goes for y, if y=0, then no instance tag is added.
     */
    final public static String INSTANCE_DELIMITER = "^{";
    final public static String STACK_DELIMITER = "_{";
    final public static String CLOSE_DELIMITER = "}";

    /**
     * @return stack depth suffix label
     */
    public String getStackSuffix() {
        return this.getStackDepthLabel() == 0 ? "" : Vertex.STACK_DELIMITER
            + String.valueOf(this.getStackDepthLabel())
            + Vertex.CLOSE_DELIMITER;
    }

    /**
     * @return depth suffix label, used to instance tagging
     */
    protected String getDepthSuffix() {
        return this.depth == 0 ? "" : Vertex.INSTANCE_DELIMITER + "(" + String.valueOf(this.depth) + ")" + Vertex.CLOSE_DELIMITER; /// STACK_DELIMITER ??
    }

    /**
     * @param disj - linear disjunction
     * @return disj without instance tags
     */
    public static LinearDisjunction removeInstanceTag(final LinearDisjunction disj) {
        return Vertex.removeTag(disj, Vertex.INSTANCE_DELIMITER);
    }

    /**
     * @param disj - linear disjunction
     * @return disj with initial variables names
     */
    public static LinearDisjunction removeFullTag(final LinearDisjunction disj) {
        return Vertex.removeTag(Vertex.removeInstanceTag(disj), Vertex.STACK_DELIMITER);
    }

    /**
     * @param disj - linear disjunction
     * @param delimiter - suffix delimiter
     * @return disj without tags started by the delimiter
     */
    public static LinearDisjunction removeTag(final LinearDisjunction disj, final String delimiter) {
        final Map<String, String> replaceMap = new HashMap<>();

        for (final String var : disj.getVariables()) {
            final int index = var.indexOf(delimiter);
            replaceMap.put(var, index < 0 ? var : var.substring(0, index));
        }

        return LinearDisjunction.create(disj.rename(replaceMap));
    }
}
