package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Transforms a conditional program into an unconditional program. <br>
 * SG07 <br>
 * Based on CTRSToQTRSProcessor
 * @author Tim Enger, Christian Kuknat
 */

public class CTRSToCSRProcessor extends Processor.ProcessorSkeleton {

    private final boolean identify;
    private final boolean eliminate;

    @ParamsViaArgumentObject
    public CTRSToCSRProcessor(final Arguments arguments) {
        this.eliminate = arguments.eliminate;
        this.identify = arguments.identify;
    }

    @Override
    public Result process(final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {

        final CTRSProblem ctrs = (CTRSProblem) obl;
        final FreshNameGenerator fg = ctrs.getFreshNameGenerator();
        final Map<FunctionSymbol, Set<Integer>> replacementMap =
            new HashMap<FunctionSymbol, Set<Integer>>();
        final Set<Rule> newRules =
            CTRSToCSRProcessor.translate(ctrs.getC(), fg, this.identify, this.eliminate);

        newRules.addAll(ctrs.getR());

        this.fillReplacementMap(ctrs, newRules, replacementMap);

        CSRProblem csrs = CSRProblem.create(newRules, replacementMap, false);

        final Proof proof = new CTRSToCSRSProof();
        return ResultFactory.proved(csrs, YNMImplication.SOUND,
            proof);
    }

    public static Set<Rule> translate(final ImmutableSet<ConditionalRule> condRules,
        final FreshNameGenerator fg,
        final boolean identify,
        final boolean eliminate) {
        // init graph
        final Graph<CondNode, TRSTerm> condGraph = new Graph<CondNode, TRSTerm>();
        // build special start node (so we have a way to reach all trees in the forest)
        final Node<CondNode> start = new Node<CondNode>(new CondNode(null));
        condGraph.addNode(start);
        // build graph
        CTRSToCSRProcessor.buildGraph(condGraph, start, condRules, identify);
        // calculate vars
        CTRSToCSRProcessor.calcVars(condGraph, start, new LinkedHashSet<TRSVariable>());
        if (eliminate) {
            // remove unneeded vars from the paths
            CTRSToCSRProcessor.elimVars(condGraph);
        }
        // label all nodes with new function symbols U, U1, U2, ...
        CTRSToCSRProcessor.calcFuns(condGraph, start, fg);
        // build rules
        final Set<Rule> newRules = new LinkedHashSet<Rule>();
        CTRSToCSRProcessor.buildRules(condGraph, start, newRules);

        return newRules;
    }

    private static void buildGraph(final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> start,
        final Set<ConditionalRule> condRules,
        final boolean identify) {
        for (final ConditionalRule condRule : condRules) {
            if (Globals.useAssertions) {
                assert (condRule.isDeterministic3CTRS());
            }
            Node<CondNode> current = start;
            TRSTerm edgeLabel = condRule.getLeft();
            for (final Condition cond : condRule.getConditions()) {
                final TRSTerm nodeLabel = cond.getLeft();
                Node<CondNode> nextNode = null;
                if (identify) {
                    // if we already have an edge with the same label to a node with the same term, reuse it
                    for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
                        if (edge.getObject().equals(edgeLabel)
                            && edge.getEndNode().getObject().getTerm().equals(
                                nodeLabel)) {
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
            final Node<CondNode> leafNode =
                new Node<CondNode>(new CondNode(condRule.getRight()));
            condGraph.addEdge(current, leafNode, edgeLabel);
        }
    }

    private static void calcVars(final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> current,
        final Set<TRSVariable> vars) {
        final CondNode condNode = current.getObject();
        condNode.setVars(vars);
        for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
            final Set<TRSVariable> newVars = new LinkedHashSet<TRSVariable>(vars);
            newVars.addAll(edge.getObject().getVariables());
            CTRSToCSRProcessor.calcVars(condGraph, edge.getEndNode(), newVars);
        }
    }

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

    private static void calcFuns(final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> current,
        final FreshNameGenerator fg) {
        final CondNode condNode = current.getObject();

        final Set<Edge<TRSTerm, CondNode>> outEdges =
            condGraph.getOutEdges(current);
        if (!outEdges.isEmpty()) {
            condNode.setF(FunctionSymbol.create(fg.getFreshName("U", false),
                1 + condNode.getVars().size()));

        }
        for (final Edge<TRSTerm, CondNode> edge : outEdges) {
            CTRSToCSRProcessor.calcFuns(condGraph, edge.getEndNode(), fg);
        }
    }

    private static void buildRules(final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> current,
        final Set<Rule> newRules) {
        final CondNode condNode = current.getObject();
        final boolean isStart = condNode.getTerm() == null;
        for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
            TRSTerm lhs = edge.getObject();
            if (!isStart) {
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.add(lhs);
                args.addAll(condNode.getVars());
                lhs =
                    TRSTerm.createFunctionApplication(
                        edge.getStartNode().getObject().getF(),
                        ImmutableCreator.create(args));
            }
            final CondNode toNode = edge.getEndNode().getObject();
            TRSTerm rhs = toNode.getTerm();
            if (toNode.getF() != null) {
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.add(rhs);
                args.addAll(toNode.getVars());
                rhs =
                    TRSTerm.createFunctionApplication(toNode.getF(),
                        ImmutableCreator.create(args));
            }
            newRules.add(Rule.create((TRSFunctionApplication) lhs, rhs));
            CTRSToCSRProcessor.buildRules(condGraph, edge.getEndNode(), newRules);
        }
    }

    public void fillReplacementMap(final CTRSProblem ctrs,
        final Set<Rule> rules,
        final Map<FunctionSymbol, Set<Integer>> replacementMap) {

        // add all function symbols from ctrs
        for (final FunctionSymbol symbol : ctrs.getSignature()) {
            final Set<Integer> newSet = new HashSet<Integer>();
            for (int i = 0; i < symbol.getArity(); i++) {
                newSet.add(i);
            }
            replacementMap.put(symbol, newSet);
        }

        // add function symbols from new rules
        final Set<Integer> newSet = new HashSet<Integer>();
        newSet.add(0);
        for (final Rule rule : rules) {
            if (!ctrs.getSignature().contains(rule.getRootSymbol())) {
                replacementMap.put(rule.getRootSymbol(), newSet);
            }

        }
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof CTRSProblem;
    }

    public static class CTRSToCSRSProof extends Proof.DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "The conditional rules have been transormed into unconditional rules according to "
                + o.cite(new Citation[] { Citation.SG07, Citation.AAECCNOC })
                + ".";
        }

    }

    public static class CondNode {

        private final TRSTerm term;
        private Set<TRSVariable> vars;
        private FunctionSymbol f;

        public CondNode(final TRSTerm term) {
            this.term = term;
            this.vars = null;
            this.f = null;
        }

        public FunctionSymbol getF() {
            return this.f;
        }

        public void setF(final FunctionSymbol f) {
            this.f = f;
        }

        public Set<TRSVariable> getVars() {
            return this.vars;
        }

        public void setVars(final Set<TRSVariable> vars) {
            this.vars = vars;
        }

        public TRSTerm getTerm() {
            return this.term;
        }

        @Override
        public String toString() {
            final StringBuilder sb = new StringBuilder();
            sb.append(this.term == null ? "START" : this.term.toString());
            sb.append(", ");
            sb.append(this.vars);
            sb.append(", ");
            sb.append(this.f);
            return sb.toString();
        }

    }

    public static class Arguments {
        // eliminate identical rules
        public boolean identify = false;
        // eliminate unneeded variables
        public boolean eliminate = false;
    }

}
