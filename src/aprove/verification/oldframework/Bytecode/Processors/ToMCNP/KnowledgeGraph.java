package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import java.math.*;
import java.util.*;

/**
 * Stores inferred constraints and allows to decide, whether or not
 * other constraints are already implied.
 * Example: If we have x > y and z <= y, then we don't need to ask
 * whether or not x > z holds, because we already know this.
 *
 * @author Matthias Hoelzel
 *
 */
public class KnowledgeGraph {
    /**
     * Set of all nodes.
     */
    private final LinkedHashSet<MCSVariable> nodes;

    /**
     * If x > y, then y is an element of strictEdges.get(x)
     */
    private final LinkedHashMap<MCSVariable, Set<MCSVariable>> strictEdges;

    /**
     * If x >= y, then y is an element of weakEdges.get(y)
     */
    private final LinkedHashMap<MCSVariable, Set<MCSVariable>> weakEdges;

    /**
     * List of all constants.
     */
    private final LinkedHashSet<BigInteger> constants;

    /**
     * Constructor: Creates an empty knowledge graph.
     */
    public KnowledgeGraph() {
        this.strictEdges = new LinkedHashMap<MCSVariable, Set<MCSVariable>>();
        this.weakEdges   = new LinkedHashMap<MCSVariable, Set<MCSVariable>>();
        this.nodes = new LinkedHashSet<MCSVariable>();
        this.constants = new LinkedHashSet<BigInteger>();
    }

    /**
     * Registers a constant.
     * @param c constant to register.
     */
    private void registerConstant(final BigInteger c) {
        if (!this.constants.contains(c)) {
            final MCSVariable varC = MCSVariable.create(c);
            this.insertNode(varC);

            for (final BigInteger other : this.constants) {
                final MCSVariable varOther = MCSVariable.create(other);
                if (c.compareTo(other) > 0) {
                    this.strictEdges.get(varOther).add(varC);
                } else {
                    this.strictEdges.get(varC).add(varOther);
                }
            }
        }
    }

    /**
     * Inserts a constraint.
     * @param ac an abstract constraint.
     */
    public void insertConstraint(final AbstractConstraint ac) {
        if (ac != null) {
            final MCSConstraint c;
            if (ac instanceof PseudoMCSConstraint) {
                final PseudoMCSConstraint pseudo = (PseudoMCSConstraint) ac;
                c = (new MCSConstraint(pseudo.left,
                        pseudo.op, MCSVariable.create(pseudo.right))).normalize();
                this.registerConstant(pseudo.right);
            } else if (ac instanceof MCSConstraint) {
                c = ((MCSConstraint) ac).normalize();
            } else {
                assert false;
                return;
            }

            this.insertNode(c.left);
            this.insertNode(c.right);

            if (c.op.equals(MCSOperator.MCS_EQ)) {
                this.insertWeakEdge(c.left, c.right);
                this.insertWeakEdge(c.right, c.left);
            } else if (c.op.equals(MCSOperator.MCS_GE)) {
                this.insertWeakEdge(c.left, c.right);
            } else if (c.op.equals(MCSOperator.MCS_G)) {
                this.insertStrictEdge(c.left, c.right);

            } else {
                assert false;
            }
        }
    }

    /**
     * Checks whether we already know, that [ac] holds.
     * @param ac an abstract constraint.
     * @return TRUE, if [ac] is implied.
     *         The given answer will only correct, if the given constraint are consistent.
     *         Example: u > u implies everything, but this is necessarily represented in the graph.
     *                  So: Do not even dare to fill in nonsense!
     */
    public boolean isImplied(final AbstractConstraint ac) {
        if (ac != null) {
            final MCSConstraint c;
            if (ac instanceof PseudoMCSConstraint) {
                final PseudoMCSConstraint pseudo = (PseudoMCSConstraint) ac;
                c = (new MCSConstraint(pseudo.left, pseudo.op,
                        MCSVariable.create(pseudo.right))).normalize();
            } else if (ac instanceof MCSConstraint) {
                c = ((MCSConstraint) ac).normalize();
            } else {
                assert false;
                return false;
            }

            if (!this.nodes.contains(c.left)
                || !this.nodes.contains(c.right)) {
                return false;
            }

            if (c.op.equals(MCSOperator.MCS_EQ)) {
                return this.weakEdges.get(c.left).contains(c.right)
                       && this.weakEdges.get(c.right).contains(c.left);
            } else if (c.op.equals(MCSOperator.MCS_GE)) {
                return this.weakEdges.get(c.left).contains(c.right);
            } else if (c.op.equals(MCSOperator.MCS_G)) {
                return this.strictEdges.get(c.left).contains(c.right);
            } else {
                assert false;
                return false;
            }
        }
        return false;
    }

    /**
     * Inserts a node.
     * @param x a MCSVariable to be inserted.
     */
    private void insertNode(final MCSVariable x) {
        this.nodes.add(x);
        if (!this.strictEdges.containsKey(x)) {
            this.strictEdges.put(x, new LinkedHashSet<MCSVariable>());
        }
        if (!this.weakEdges.containsKey(x)) {
            final Set<MCSVariable> newWeakEdges = new LinkedHashSet<MCSVariable>();
            newWeakEdges.add(x);
            this.weakEdges.put(x, newWeakEdges);
        }
    }

    /**
     * Insert a weak edge from [from] to [to].
     * @param from MCSVariable
     * @param to MCSVariable
     */
    private void insertWeakEdge(final MCSVariable from, final MCSVariable to) {
        // 1. Get everything we know about [to]:
        final Set<MCSVariable> toStricts = this.strictEdges.get(to);
        final Set<MCSVariable> toWeaks = this.weakEdges.get(to);

        // 2. Insert new edges:
        for (final MCSVariable x : this.nodes) {
            final Set<MCSVariable> xWeaks = this.weakEdges.get(x);
            final Set<MCSVariable> xStricts = this.strictEdges.get(x);

            if (xStricts.contains(from)) {
                xStricts.addAll(toWeaks);
                xWeaks.addAll(toWeaks);
            } else if (xWeaks.contains(from)) {
                xStricts.addAll(toStricts);
                xWeaks.addAll(toWeaks);
            }
        }
    }

    /**
     * Insert a strict edge from [from] to [to].
     * @param from MCSVariable
     * @param to MCSVariable
     */
    private void insertStrictEdge(final MCSVariable from, final MCSVariable to) {
        // 1. Get everything we need to know about [to]:
        final Set<MCSVariable> toWeaks = this.weakEdges.get(to);

        // 2. Insert new edges:
        for (final MCSVariable x : this.nodes) {
            final Set<MCSVariable> xWeaks = this.weakEdges.get(x);
            final Set<MCSVariable> xStricts = this.strictEdges.get(x);

            if (xWeaks.contains(from)) {
                xStricts.addAll(toWeaks);
                xWeaks.addAll(toWeaks);
            }
        }
    }

    @Override
    public String toString() {
        final StringBuilder result = new StringBuilder("KnowledgeGraph {\nNodes = ");
        result.append(this.nodes);
        result.append("\nWeak Edges:\n");
        for (final MCSVariable x : this.nodes) {
            final Set<MCSVariable> weaks = this.weakEdges.get(x);
            result.append(x.toString());
            result.append(": ");
            result.append(weaks);
            result.append("\n");
        }
        result.append("Strict Edges:\n");
        for (final MCSVariable x : this.nodes) {
            final Set<MCSVariable> stricts = this.strictEdges.get(x);
            result.append(x.toString());
            result.append(": ");
            result.append(stricts);
            result.append("\n");
        }
        result.append("}\n");
        return result.toString();
    }
}
