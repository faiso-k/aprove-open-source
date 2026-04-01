package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

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
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.xml.*;
import immutables.*;

/** Transforms a conditional Program into an unconditional program.
 * <p>
 * Enno Ohlebusch, "Advanced Topics in Term Rewriting", p. 212
 * @author Stephan Falke
 * @version $Id$
 */
public class CTRSToQTRSProcessor extends Processor.ProcessorSkeleton {

    private final boolean identify;
    private final boolean eliminate;

    @Override
    public Result process(final BasicObligation obl, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final CTRSProblem ctrs = (CTRSProblem) obl;
        final FreshNameGenerator fg = ctrs.getFreshNameGenerator();
        final Map<ConditionalRule, List<Rule>> mapping = new LinkedHashMap<>();
        final Set<Rule> newRules = CTRSToQTRSProcessor.translate(ctrs.getC(), fg, this.identify, this.eliminate, mapping);
        newRules.addAll(ctrs.getR());
        final QTRSProblem qtrs = QTRSProblem.create(ImmutableCreator.create(newRules));
        final Proof proof = new CTRSToQTRSProof(ctrs, mapping);
        return ResultFactory.proved(qtrs, YNMImplication.SOUND, proof);
    }

    public static Set<Rule> translate(
        final ImmutableSet<ConditionalRule> condRules,
        final FreshNameGenerator fg,
        final boolean identify,
        final boolean eliminate,
        final Map<ConditionalRule, List<Rule>> mapping)
    {
        // init graph
        final Graph<CondNode, TRSTerm> condGraph = new Graph<CondNode, TRSTerm>();
        // build special start node (so we have a way to reach all trees in the forest)
        final Node<CondNode> start = new Node<CondNode>(new CondNode(null, null));
        condGraph.addNode(start);
        // build graph
        CTRSToQTRSProcessor.buildGraph(condGraph, start, condRules, identify);
        // calculate vars
        CTRSToQTRSProcessor.calcVars(condGraph, start, new LinkedHashSet<TRSVariable>());
        if (eliminate) {
            // remove unneeded vars from the paths
            CTRSToQTRSProcessor.elimVars(condGraph);
        }
        // label all nodes with new function symbols U, U1, U2, ...
        CTRSToQTRSProcessor.calcFuns(condGraph, start, fg);
        // build rules
        final Set<Rule> newRules = new LinkedHashSet<Rule>();
        CTRSToQTRSProcessor.buildRules(condGraph, start, newRules, mapping, null, null);
        return newRules;
    }

    private static void buildGraph(final Graph<CondNode, TRSTerm> condGraph, final Node<CondNode> start, final Set<ConditionalRule> condRules, final boolean identify) {
        for (final ConditionalRule condRule : condRules) {
            if (Globals.useAssertions) {
                assert(condRule.isDeterministic3CTRS());
            }
            Node<CondNode> current = start;
            TRSTerm edgeLabel = condRule.getLeft();
            for (final Condition cond : condRule.getConditions()) {
                final TRSTerm nodeLabel = cond.getLeft();
                Node<CondNode> nextNode = null;
                if (identify) {
                    // if we already have an edge with the same label to a node with the same term, reuse it
                    for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
                        if (edge.getObject().equals(edgeLabel) && edge.getEndNode().getObject().getTerm().equals(nodeLabel)) {
                            nextNode = edge.getEndNode();
                            nextNode.getObject().rules.add(condRule);
                            break;
                        }
                    }
                }
                if (nextNode == null) {
                    // if we do not reuse an existing node, build a new one and add a corresponding edge
                    nextNode = new Node<CondNode>(new CondNode(condRule, nodeLabel));
                    condGraph.addEdge(current, nextNode, edgeLabel);
                }
                current = nextNode;
                edgeLabel = cond.getRight();
            }
            final Node<CondNode> leafNode = new Node<CondNode>(new CondNode(condRule, condRule.getRight()));
            condGraph.addEdge(current, leafNode, edgeLabel);
        }
    }

    private static void calcVars(final Graph<CondNode, TRSTerm> condGraph, final Node<CondNode> current, final Set<TRSVariable> vars) {
        final CondNode condNode = current.getObject();
        condNode.setVars(vars);
        for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
            final Set<TRSVariable> newVars = new LinkedHashSet<TRSVariable>(vars);
            newVars.addAll(edge.getObject().getVariables());
            CTRSToQTRSProcessor.calcVars(condGraph, edge.getEndNode(), newVars);
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

    private static void calcFuns(final Graph<CondNode, TRSTerm> condGraph, final Node<CondNode> current, final FreshNameGenerator fg) {
        final CondNode condNode = current.getObject();
        final Set<Edge<TRSTerm, CondNode>> outEdges = condGraph.getOutEdges(current);
        if (!outEdges.isEmpty()) {
            condNode.setF(FunctionSymbol.create(fg.getFreshName("U", false), 1+condNode.getVars().size()));
        }
        for (final Edge<TRSTerm, CondNode> edge : outEdges) {
            CTRSToQTRSProcessor.calcFuns(condGraph, edge.getEndNode(), fg);
        }
    }

    private static void buildRules(
        final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> current,
        final Set<Rule> newRules,
        final Map<ConditionalRule, List<Rule>> mapping,
        List<Rule> partialListOfRules,
        final ConditionalRule condRule)
    {
        final CondNode condNode = current.getObject();
        if (condRule == null) {
            for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
                for (final ConditionalRule rule : edge.getEndNode().getObject().rules) {
                    CTRSToQTRSProcessor.buildRules(condGraph, current, newRules, mapping, partialListOfRules, rule);
                }
            }
            return;
        }
        final boolean isStart = condNode.getTerm() == null;
        for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
            if (!edge.getEndNode().getObject().rules.contains(condRule)) {
                continue;
            }
            if (isStart) {
                partialListOfRules = new ArrayList<>();
            }
            TRSTerm lhs = edge.getObject();
            if (!isStart) {
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.add(lhs);
                args.addAll(condNode.getVars());
                lhs = TRSTerm.createFunctionApplication(edge.getStartNode().getObject().getF(), ImmutableCreator.create(args));
            }
            final CondNode toNode = edge.getEndNode().getObject();
            TRSTerm rhs = toNode.getTerm();
            final boolean isEnd = toNode.getF() == null;
            if (!isEnd) {
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.add(rhs);
                args.addAll(toNode.getVars());
                rhs = TRSTerm.createFunctionApplication(toNode.getF(), ImmutableCreator.create(args));
            }
            final Rule newRule = Rule.create((TRSFunctionApplication) lhs, rhs);
            newRules.add(newRule);
            partialListOfRules.add(newRule);
            if (isEnd) {
                mapping.put(condRule, partialListOfRules);
            } else {
                CTRSToQTRSProcessor.buildRules(condGraph, edge.getEndNode(), newRules, mapping, partialListOfRules, condRule);
            }
        }
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof CTRSProblem;
    }

    @ParamsViaArgumentObject
    public CTRSToQTRSProcessor(final Arguments arguments) {
        this.eliminate = arguments.eliminate;
        this.identify = arguments.identify;
    }

    public static class CTRSToQTRSProof extends Proof.DefaultProof {

        private final CTRSProblem orig;
        private final Map<ConditionalRule, List<Rule>> mapping;

        public CTRSToQTRSProof(final CTRSProblem orig, final Map<ConditionalRule,List<Rule>> mapping) {
            this.orig = orig;
            this.mapping = mapping;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "The conditional rules have been transormed into unconditional rules according to "+o.cite(new Citation[]{Citation.CTRS, Citation.AAECCNOC})+".";
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            final Element info = CPFTag.UNRAVEL_INFO.create(doc);
            for (final Rule rule : this.orig.getR()) {
                ConditionalRule crule = ConditionalRule.create(rule);
                info.appendChild(CPFTag.UNRAVEL_ENTRY.create(
                    doc,
                    crule.toCPF(doc, xmlMetaData, CPFTag.CONDITIONAL_RULE),
                    rule.toCPF(doc, xmlMetaData)));
            }
            for (final Map.Entry<ConditionalRule, List<Rule>> c_to_rls : this.mapping.entrySet()) {
                ConditionalRule crule = c_to_rls.getKey();
                final Element entry = CPFTag.UNRAVEL_ENTRY.create(doc, crule.toCPF(doc, xmlMetaData, CPFTag.CONDITIONAL_RULE));
                for (final Rule rule : c_to_rls.getValue()) {
                    entry.appendChild(rule.toCPF(doc, xmlMetaData));
                }
                info.appendChild(entry);
            }
            return CPFTag.QUASI_REDUCTIVE_PROOF.create(doc, CPFTag.UNRAVELING.create(doc, info, childrenProofs[0]));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }


    public static class CondNode {

        private final Set<ConditionalRule> rules;
        private final TRSTerm term;
        private Set<TRSVariable> vars;
        private FunctionSymbol f;

        public CondNode(final TRSTerm term) {
            this(null, term);
        }

        public CondNode(final ConditionalRule rule, final TRSTerm term) {
            this.rules = new HashSet<ConditionalRule>();
            if (rule != null) {
                this.rules.add(rule);
            }
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
        public boolean identify = true;
        public boolean eliminate = true;
    }

}
