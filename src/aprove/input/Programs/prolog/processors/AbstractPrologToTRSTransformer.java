package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Condition.*;
import aprove.verification.dpframework.TRSProblem.Processors.CTRSToQTRSProcessor.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public abstract class AbstractPrologToTRSTransformer extends PrologProblemProcessor {

    public class PrologToTRSProofs extends Proof.DefaultProof {
        Collection<Proof> proofs;

        public PrologToTRSProofs(final Collection<Proof> proofs) {
            this.proofs = proofs;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Utility.VerbosityExportable#export(aprove.verification.oldframework.Utility.Export_Util, aprove.verification.oldframework.Utility.VerbosityLevel)
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            for (final Proof p : this.proofs) {
                res.append(p.export(o, level));
                res.append(o.newline());
            }
            return res.toString();
        }
    }

    protected static final Logger logger = Logger.getLogger("aprove.verification.dpframework.PROLOGProblem.Processors");
    protected boolean eliminate = true;

    protected boolean identify = true;

    /**
     * Creates a ConditionalRule out of the specified clause using the specified
     * FreshNameGenerator to avoid conflicts due to the use of the same names
     * for different objects.
     * @param clause The PrologClause from which to build a rule.
     * @param fridge The FreshNameGenerator.
     * @return A new ConditionalRule built from this clause.
     */
    protected static ConditionalRule toConditionalRule(final PrologClause clause, final PrologFNG fridge) {
        final ImmutableArrayList<? extends TRSTerm> args =
            AbstractPrologToTRSTransformer.createTermsForGeneralizedRule(clause.getHead(), fridge);
        return ConditionalRule.create(
            TRSTerm.createFunctionApplication(fridge.createInFunctionSymbol(clause.getHead()), args),
            TRSTerm.createFunctionApplication(fridge.createOutFunctionSymbol(clause.getHead()), args),
            clause.getBody() == null
                ? ImmutableCreator.create(new ArrayList<Condition>())
                    : AbstractPrologToTRSTransformer.toConditions(clause.getBody(), fridge));
    }

    /**
     * Transforms a given set of ConditionalRules to a set of GeneralizedRules.
     * @param condRules The set of ConditionalRules to transform.
     * @param fg A FreshNameGenerator for avoiding name conflicts.
     * @return A set of GeneralizedRules computed from the given
     * ConditionalRules.
     */
    protected static Pair<Set<GeneralizedRule>, Set<FunctionSymbol>> translate(
        final ImmutableSet<ConditionalRule> condRules,
        final PrologFNG fg,
        final boolean identify,
        final boolean eliminate)
    {
        // init graph
        final Graph<CondNode, TRSTerm> condGraph = new Graph<CondNode, TRSTerm>();
        // build special start node (so we have a way to reach all trees in the forest)
        final Node<CondNode> start = new Node<CondNode>(new CondNode(null));
        condGraph.addNode(start);
        // build graph
        AbstractPrologToTRSTransformer.buildGraph(condGraph, start, condRules, identify);
        // calculate vars
        AbstractPrologToTRSTransformer.calcVars(condGraph, start, new LinkedHashSet<TRSVariable>());
        if (eliminate) {
            // remove unneeded vars from the paths
            AbstractPrologToTRSTransformer.elimVars(condGraph);
        }
        // label all nodes with new function symbols U, U1, U2, ...
        final Set<FunctionSymbol> newFuncs = new LinkedHashSet<FunctionSymbol>();
        AbstractPrologToTRSTransformer.calcFuns(condGraph, start, fg, newFuncs);
        // build rules
        final Set<GeneralizedRule> newRules = new LinkedHashSet<GeneralizedRule>();
        AbstractPrologToTRSTransformer.buildRules(condGraph, start, newRules);
        return new Pair<Set<GeneralizedRule>, Set<FunctionSymbol>>(newRules, newFuncs);
    }

    /**
     * Transforms the given set of ConditionalRules into a graph. The start node
     * of the graph is specified by the start argument. For every
     * ConditionalRule of the given set nodes and edges are added in the
     * following way: The left side of the ConditionalRule is the label for the
     * outgoing edge from the start node. The node reached with this edge is
     * labeled with the left side of the first condition (or the right side of
     * the ConditionalRule if no conditions exist for this rule). Then the
     * conditions are transformed in the way that every right side of a
     * condition is the label for an outgoing edge from the node labeled with
     * this condition's left side to a node labeled with the left side of the
     * next condition. The last condition's edge (labeled with its right side)
     * leads to a node labeled with the right side of the ConditionalRule. So
     * all edges but the first from the start node are labeled with the right
     * sides of the conditions while the first edge is labeled with the left
     * side of the ConditionalRule. All nodes but the last are labeled with the
     * left sides of the conditions while the last node is labeled with the
     * right side of the ConditionalRule. If the identify flag is set then edges
     * will be reused if the labels of the edge and the end node of this edge
     * are equal to the labels of a new edge and its end node.
     * @param condGraph The graph to be built (should only contain the start
     * node).
     * @param start The start node for the graph.
     * @param condRules The set of ConditionalRules to be transformed into the
     * graph.
     * @param identify Flag to indicate if edges should be reused.
     */
    private static void buildGraph(
        final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> start,
        final Set<ConditionalRule> condRules,
        final boolean identify)
    {
        for (final ConditionalRule condRule : condRules) {
            Node<CondNode> current = start;
            TRSTerm edgeLabel = condRule.getLeft();
            for (final Condition cond : condRule.getConditions()) {
                final TRSTerm nodeLabel = cond.getLeft();
                Node<CondNode> nextNode = null;
                if (identify) {
                    // if we already have an edge with the same label to a node with the same term, reuse it
                    for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
                        if (edge.getObject().equals(edgeLabel)
                            && edge.getEndNode().getObject().getTerm().equals(nodeLabel))
                        {
                            nextNode = edge.getEndNode();
                            break;
                        }
                    }
                }
                if (nextNode == null) {
                    // if we do not reuse an existing node, build a new one and add a corresponding edge
                    nextNode = new Node<CondNode>(new CondNode(nodeLabel));
                    condGraph.addEdge(current, nextNode, edgeLabel);
                }
                current = nextNode;
                edgeLabel = cond.getRight();
            }
            final Node<CondNode> leafNode = new Node<CondNode>(new CondNode(condRule.getRight()));
            condGraph.addEdge(current, leafNode, edgeLabel);
        }
    }

    /*- translation to trs ---------------------------------------------------*/

    /**
     * Transforms the given graph in a set of GeneralizedRules.<br>
     * <br>
     * The graph must be prepared in the way that new FunctionSymbols have been
     * created by invoking the calcFuns() method.<br>
     * <br>
     * This method traverses the graph and builds new GeneralizedRules in the
     * following way:<br>
     * The left side of the rule is the label of the first edge in case of the
     * start node and a new FunctionApplication built from the new
     * FunctionSymbol of the next edge and the variables in use at the current
     * node followed by the next edge's label as arguments otherwise. The right
     * side of the rule is the label of the edge's end node in case of the last
     * node and a new FunctionApplication built from the new FunctionSymbol of
     * the end node and its variables in use and its label as arguments
     * otherwise. Speaking in terms of ConditionalRules the GeneralizedRules are
     * constructed by using the left side of the ConditionalRule as left side of
     * the first GeneralizedRule and the helping FunctionApplications as left
     * sides of all other GeneralizedRules for this ConditionalRule. The right
     * side of the last GeneralizedRule is the right side of the ConditionalRule
     * and the right side of all other GeneralizedRules are the helping
     * FunctionApplications. The helping FunctionApplications have the next
     * condition's left side as argument if they are on a right side in the
     * GeneralizedRule and the next condition's right side as argument if they
     * are on the left side of the GeneralizedRule - always after the variables
     * in use as arguments.<br>
     * <br>
     * This method should be called on the start node as current node and an
     * empty set of GeneralizedRules.
     * @param condGraph The graph to transform.
     * @param current The current node to process.
     * @param newRules The set of GeneralizedRules to which the new rules are
     * added.
     */
    private static void buildRules(
        final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> current,
        final Set<GeneralizedRule> newRules)
    {
        final CondNode condNode = current.getObject();
        final boolean isStart = condNode.getTerm() == null;
        for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
            TRSTerm lhs = edge.getObject();
            if (!isStart) {
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.addAll(condNode.getVars());
                args.add(lhs);
                lhs =
                    TRSTerm.createFunctionApplication(
                        edge.getStartNode().getObject().getF(),
                        ImmutableCreator.create(args));
            }
            final CondNode toNode = edge.getEndNode().getObject();
            TRSTerm rhs = toNode.getTerm();
            if (toNode.getF() != null) {
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.addAll(toNode.getVars());
                args.add(rhs);
                rhs = TRSTerm.createFunctionApplication(toNode.getF(), ImmutableCreator.create(args));
            }
            newRules.add(GeneralizedRule.create((TRSFunctionApplication) lhs, rhs));
            AbstractPrologToTRSTransformer.buildRules(condGraph, edge.getEndNode(), newRules);
        }
    }

    /**
     * Prepares the given graph for the transformation in GeneralizedRules
     * through calculating new FunctionSymbols for helping FunctionApplications.
     * The names for the new FunctionSymbols are generated with the given
     * FreshNameGenerator deriving from "U". This method should be first called
     * with the start node as current node.
     * @param condGraph The graph to prepare.
     * @param current The current node to process.
     * @param fg The FreshNameGenerator for new names.
     */
    private static void calcFuns(
        final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> current,
        final PrologFNG fg,
        final Set<FunctionSymbol> newFuncs)
    {
        final CondNode condNode = current.getObject();
        final Set<Edge<TRSTerm, CondNode>> outEdges = condGraph.getOutEdges(current);
        if (!outEdges.isEmpty()) {
            final FunctionSymbol newFunc =
                FunctionSymbol.create(fg.getFreshName("U", false), 1 + condNode.getVars().size());
            condNode.setF(newFunc);
            newFuncs.add(newFunc);
        }
        for (final Edge<TRSTerm, CondNode> edge : outEdges) {
            AbstractPrologToTRSTransformer.calcFuns(condGraph, edge.getEndNode(), fg, newFuncs);
        }
    }

    /**
     * Computes the set of variables used along a path through the graph. The
     * current node's variables are set to the given set of variables. Then for
     * all outgoing edges from the current node a new set of variables is
     * created with the variables of the next edge's term in addition to all old
     * variables. The method is then recursively called with this new set of
     * variables and the end node of the edge. This method should be first
     * called with the start node and an empty set of variables.
     * @param condGraph The graph in which the variables are computed.
     * @param current The current node.
     * @param vars The set of already computed variables.
     */
    private static void calcVars(
        final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> current,
        final Set<TRSVariable> vars)
    {
        final CondNode condNode = current.getObject();
        condNode.setVars(vars);
        for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
            final Set<TRSVariable> newVars = new LinkedHashSet<TRSVariable>(vars);
            newVars.addAll(edge.getObject().getVariables());
            AbstractPrologToTRSTransformer.calcVars(condGraph, edge.getEndNode(), newVars);
        }
    }

    /**
     * Creates an ArrayList of Terms out of the specified ArrayList of
     * PrologTerms using the toConstructorTerm() method for every PrologTerm in
     * the list.
     * @param arguments The list of PrologTerms to transform.
     * @param fridge
     * @return An ArrayList of Terms built from the given PrologTerms.
     */
    private static ArrayList<TRSTerm> createConstructorTermsForGeneralizedRule(
        final List<PrologTerm> arguments,
        final PrologFNG fridge)
    {
        final ArrayList<TRSTerm> res = new ArrayList<TRSTerm>();
        for (final PrologTerm arg : arguments) {
            res.add(AbstractPrologToTRSTransformer.toConstructorTerm(arg, fridge));
        }
        return res;
    }

    /**
     * Creates an ImmutableArrayList of Terms out of the specified term's
     * arguments for use as arguments in GeneralizedRules.
     * @param term The PrologTerm from which to build terms.
     * @return An ImmutableArrayList of Terms built from this term's arguments.
     */
    private static ImmutableArrayList<? extends TRSTerm> createTermsForGeneralizedRule(
        final PrologTerm term,
        final PrologFNG fridge)
    {
        final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        for (final PrologTerm t : term.getArguments()) {
            if (t.isVariable()) {
                args.add(TRSTerm.createVariable(t.getName()));
            } else {
                final ArrayList<TRSTerm> termArgs =
                    AbstractPrologToTRSTransformer.createConstructorTermsForGeneralizedRule(t.getArguments(), fridge);
                args.add(TRSTerm.createFunctionApplication(
                    FunctionSymbol.create(fridge.getFreshName(t.getName(), true), t.getArity()),
                    ImmutableCreator.create(termArgs)));
            }
        }
        return ImmutableCreator.create(args);
    }

    /**
     * Eliminates all variables along the graph that are not used anymore from
     * the current position on. Therefore the nodes are processed in the order
     * of their ranks beginning with rank 0. For every such node a new empty set
     * of variables is created and then for all outgoing edges the variables of
     * the edges' end nodes are added. Afterwards the retainAll() method is
     * called for the current node's set of variables with the created set as
     * argument.
     * @param condGraph The graph in which the variables should be eliminated.
     */
    private static void elimVars(final Graph<CondNode, TRSTerm> condGraph) {
        for (final Set<Node<CondNode>> rank : condGraph.getRanks()) {
            for (final Node<CondNode> node : rank) {
                final CondNode condNode = node.getObject();
                final TRSTerm term = condNode.getTerm();
                if (term == null) {
                    // we have reached the root node
                    break;
                }
                final Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
                for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(node)) {
                    final CondNode toNode = edge.getEndNode().getObject();
                    vars.addAll(toNode.getTerm().getVariables());
                    vars.addAll(toNode.getVars());
                }
                condNode.getVars().retainAll(vars);
            }
        }
    }

    /*- conditional rules ----------------------------------------------------*/

    /**
     * Creates an ImmutableList of Conditions out of the specified term using
     * the specified FreshNameGenerator to avoid conflicts due to the use of the
     * same names for different objects.
     * @param term The PrologTerm to be transformed.
     * @param f The FreshNameGenerator.
     * @return An ImmutableList of Conditions built from this term.
     */
    private static ImmutableList<Condition> toConditions(final PrologTerm term, final PrologFNG fridge) {
        final List<Condition> conditions = new ArrayList<Condition>();
        term.walkConjunction(new TermWalker() {

            @Override
            public boolean goDeeper(final PrologTerm term) {
                return false;
            }

            @Override
            public boolean isApplicable(final PrologTerm term) {
                return true;
            }

            @Override
            public void performAction(final PrologTerm term) {
                final ImmutableArrayList<? extends TRSTerm> args =
                    AbstractPrologToTRSTransformer.createTermsForGeneralizedRule(term, fridge);
                conditions.add(Condition.create(
                    TRSTerm.createFunctionApplication(fridge.createInFunctionSymbol(term), args),
                    TRSTerm.createFunctionApplication(fridge.createOutFunctionSymbol(term), args),
                    ConditionType.ARROW));
            }

        });
        return ImmutableCreator.create(conditions);
    }

    /**
     * Creates a Term out of the specified PrologTerm interpreting every
     * FunctionSymbol as constructor symbol.
     * @param term The PrologTerm from which to build a Term.
     * @param fridge
     * @return A Term built from the specified PrologTerm, where all
     * FunctionApplications are seen as constructors.
     */
    private static TRSTerm toConstructorTerm(final PrologTerm term, final PrologFNG fridge) {
        return term.isVariable() ? TRSTerm.createVariable(term.getName()) : TRSTerm.createFunctionApplication(
            FunctionSymbol.create(fridge.getFreshName(term.getName(), true), term.getArity()),
            ImmutableCreator.create(AbstractPrologToTRSTransformer.createConstructorTermsForGeneralizedRule(
                term.getArguments(),
                fridge)));
    }

    abstract public Pair<BasicObligation, Proof> calculateTRSProblem(PrologProblem pp, Afs pi, PrologFNG fridge);

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return PrologProgram.isLogicProgram(pp.getProgram())
            && pp.getQuery().getPurpose().equals(PrologPurpose.TERMINATION);
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        final List<BasicObligation> obligations = new ArrayList<BasicObligation>();
        final List<Proof> proofs = new ArrayList<Proof>();
        final List<Afs> piList = pp.createListOfAfs();
        for (final Afs pi : piList) {
            final PrologFNG fridge = new PrologFNG(new LinkedHashSet<String>(), FreshNameGenerator.PROLOG_FUNCS);
            final Pair<BasicObligation, Proof> result = this.calculateTRSProblem(pp, pi, fridge);
            obligations.add(result.x);
            proofs.add(result.y);
        }
        final YNMImplication implication = YNMImplication.SOUND;
        if (obligations.size() == 1) {
            return ResultFactory.proved(obligations.get(0), implication, proofs.get(0));
        }
        final Proof proof = new PrologToTRSProofs(proofs);
        return ResultFactory.provedAnd(obligations, implication, proof);
    }
}
