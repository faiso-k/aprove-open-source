package aprove.verification.dpframework.CLSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CLSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class CLSSlicingProcessor extends CLSProcessor {

    private static final Logger LOG = Logger.getLogger("aprove.DPFrameworlk.CLSProblem.Processor.CLSSlicingProcessor");

    public static final boolean PROP_CHANGES = true;
    public static final boolean PROP_CONDS = false;

    /**
     * In some cases, slicing generates conditional rules where the condition
     * contains variables, which do not occur on the lhs. If this option is
     * set to <code>true</code>, the processor removes such variables even
     * from the condition. This takes additional time and may result in weaker
     * conditions.
     */
    public final boolean restoreVarCondition;

    private final boolean SCCs; // only SCCs are relevant?

    @ParamsViaArgumentObject
    public CLSSlicingProcessor(final Arguments arguments) {
        this.restoreVarCondition = arguments.restoreVarCondition;
        this.SCCs = arguments.SCCs;
    }

    @Override
    public boolean isCLSApplicable(final CLSProblem obl) {
        return true;
    }

    @Override
    protected Result processCLS(final CLSProblem problem, final Abortion aborter) throws AbortionException {
        final CLSProblem cls = this.sliceCLS(problem);
        return ResultFactory.proved(cls, YNMImplication.SOUND, new CLSSlicingProof());
    }

    private CLSProblem sliceCLS(final CLSProblem problem) {
        Graph<Block, ConditionalRule> graph = new Graph<Block, ConditionalRule>();
        CLSSlicingProcessor.buildGraph(graph, problem.getRules());
        final Set<Node<Block>> reachableNodes = new HashSet<Node<Block>>();
        final Stack<Node<Block>> todo = new Stack<Node<Block>>();
        for (final TRSTerm initial : problem.getInitialTerms()) {
            final Node<Block> initialNode =
                graph.getNodeFromObject(new Block(((TRSFunctionApplication) initial).getRootSymbol()));
            todo.push(initialNode);
        }
        while (!todo.isEmpty()) {
            final Node<Block> node = todo.pop();
            if (!reachableNodes.contains(node)) {
                reachableNodes.add(node);
                for (final Node<Block> succNode : graph.getOut(node)) {
                    todo.push(succNode);
                }
            }
        }
        graph = graph.getSubGraph(reachableNodes);
        while (true) {
            final boolean changed = CLSSlicingProcessor.propagateGraph(graph);
            if (!changed) {
                break;
            }
        }
        if (this.SCCs) {
            final Set<Node<Block>> sccNodes = new LinkedHashSet<Node<Block>>();
            for (final Cycle<Block> scc : graph.getSCCs()) {
                sccNodes.addAll(scc);
            }
            graph = graph.getSubGraph(sccNodes);
        }
        final CLSArguments newArgs = this.filterRules(graph, problem.getInitialTerms());
        final CLSProblem newProblem = CLSProblem.create(newArgs.rules, newArgs.initialTerms);
        return newProblem;
    }

    private CLSArguments filterRules(
        final Graph<Block, ConditionalRule> graph,
        final Set<TRSFunctionApplication> initialTerms)
    {
        final Afs afs = new Afs();
        final Set<ConditionalRule> newRules = new LinkedHashSet<ConditionalRule>();
        for (final Node<Block> node : graph.getNodes()) {
            final Block block = node.getObject();
            afs.setFiltering(block.getBlockSymbol(), block.getNeeded());
        }
        for (final Edge<ConditionalRule, Block> edge : graph.getEdges()) {
            final ConditionalRule rule = edge.getObject();
            final TRSFunctionApplication newLeft = (TRSFunctionApplication) afs.filterTerm(rule.getLeft());
            final TRSFunctionApplication newRight = (TRSFunctionApplication) afs.filterTerm(rule.getRight());
            final ImmutableList<Condition> newConds = this.filterCond(newLeft, newRight, rule.getConditions());
            newRules.add(ConditionalRule.create(newLeft, newRight, newConds));
        }

        final Set<TRSFunctionApplication> newInitialTerms = new LinkedHashSet<TRSFunctionApplication>();
        for (final TRSFunctionApplication fa : initialTerms) {
            newInitialTerms.add((TRSFunctionApplication) afs.filterTerm(fa));
        }

        return new CLSArguments(newRules, newInitialTerms);
    }

    // FIXME: make private
    static boolean propagateGraph(final Graph<Block, ConditionalRule> graph) {
        boolean changed = false;
        final Set<TRSVariable> relevantVars = new HashSet<TRSVariable>();
        if (CLSSlicingProcessor.PROP_CHANGES) {
            final Set<TRSVariable> condsVars = new HashSet<TRSVariable>();
            for (final Edge<ConditionalRule, Block> edge : graph.getEdges()) {
                for (final Condition cond : edge.getObject().getConditions()) {
                    condsVars.addAll(cond.getVariables());
                }
            }
            for (final Node<Block> node : graph.getNodes()) {
                final Block block = node.getObject();
                final int arity = block.getBlockSymbol().getArity();
                for (final Edge<ConditionalRule, Block> predEdge : graph.getInEdges(node)) {
                    for (final Edge<ConditionalRule, Block> succEdge : graph.getOutEdges(node)) {
                        final TRSFunctionApplication predRight = (TRSFunctionApplication) predEdge.getObject().getRight();
                        final List<? extends TRSTerm> predArgs = predRight.getArguments();
                        final TRSFunctionApplication succLeft = succEdge.getObject().getLeft();
                        final List<? extends TRSTerm> succArgs = succLeft.getArguments();
                        for (int i = 0; i < arity; i++) {
                            if (!predArgs.get(i).equals(succArgs.get(i))) {
                                final Set<TRSVariable> vars = predArgs.get(i).getVariables();
                                vars.addAll(succArgs.get(i).getVariables());
                                vars.retainAll(condsVars);
                                if (!vars.isEmpty()) {
                                    relevantVars.addAll(vars);
                                    changed = block.setNeeded(i) || changed;
                                }
                            }
                        }
                    }
                }
            }
        }
        for (final Set<Node<Cycle<Block>>> nodess : new SCCGraph<Block, ConditionalRule>(
            graph.getSCCs(false),
            graph,
            false).getRanks())
        {
            for (final Node<Cycle<Block>> nodes : nodess) {
                for (final Node<Block> node : nodes.getObject()) {
                    final Block block = node.getObject();
                    final FunctionSymbol blockSymbol = block.getBlockSymbol();
                    final int arity = blockSymbol.getArity();
                    if (graph.getOut(node).isEmpty()) {
                        // we are in an exit
                        for (int i = 0; i < arity; i++) {
                            final boolean status = block.getNeeded(i);
                            changed = block.setNeeded(i) || changed;
                        }
                    }
                    for (final Edge<ConditionalRule, Block> edge : graph.getInEdges(node)) {
                        final ConditionalRule rule = edge.getObject();
                        final Set<TRSVariable> neededVars = new LinkedHashSet<TRSVariable>();
                        final List<? extends TRSTerm> rightArgs = ((TRSFunctionApplication) rule.getRight()).getArguments();
                        for (int i = 0; i < arity; i++) {
                            if (block.getNeeded(i)) {
                                final Set<TRSVariable> rightIVars = rightArgs.get(i).getVariables();
                                relevantVars.addAll(rightIVars);
                                neededVars.addAll(rightIVars);
                            }
                        }
                        for (final Condition cond : rule.getConditions()) {
                            final Set<TRSVariable> condVars = cond.getVariables();
                            if (CLSSlicingProcessor.PROP_CONDS) {
                                relevantVars.addAll(condVars);
                                neededVars.addAll(condVars);
                            } else {
                                final Set<TRSVariable> intersection = new HashSet<TRSVariable>(condVars);
                                intersection.retainAll(neededVars);
                                if (!intersection.isEmpty()) {
                                    relevantVars.addAll(condVars);
                                    neededVars.addAll(condVars);
                                }
                            }
                        }
                        final Block predBlock = edge.getStartNode().getObject();
                        final FunctionSymbol predSymbol = predBlock.getBlockSymbol();
                        final int predArity = predSymbol.getArity();
                        final List<? extends TRSTerm> leftArgs = (rule.getLeft()).getArguments();
                        for (int i = 0; i < predArity; i++) {
                            if (!predBlock.getNeeded(i)) {
                                final Set<TRSVariable> predVars = leftArgs.get(i).getVariables();
                                predVars.retainAll(neededVars);
                                if (!predVars.isEmpty()) {
                                    final boolean status = predBlock.getNeeded(i);
                                    changed = predBlock.setNeeded(i) || changed;
                                }
                            }
                        }
                    }
                }
            }
        }
        for (final Edge<ConditionalRule, Block> edge : new LinkedHashSet<Edge<ConditionalRule, Block>>(graph.getEdges()))
        {
            final ConditionalRule rule = edge.getObject();
            final List<Condition> oldConds = rule.getConditions();
            if (!oldConds.isEmpty()) {
                final List<Condition> newConds = new ArrayList<Condition>(oldConds.size());
                for (final Condition cond : edge.getObject().getConditions()) {
                    final Set<TRSVariable> condVars = cond.getVariables();
                    if (relevantVars.containsAll(condVars)) {
                        newConds.add(cond);
                    }
                }
                if (newConds.size() < oldConds.size()) {
                    final ConditionalRule newRule =
                        ConditionalRule.create(rule.getLeft(), rule.getRight(), ImmutableCreator.create(newConds));
                    final Node<Block> startNode = edge.getStartNode();
                    final Node<Block> endNode = edge.getEndNode();
                    graph.removeEdge(startNode, endNode);
                    graph.addEdge(startNode, endNode, newRule);
                }
            }
        }
        return changed;
    }

    // FIXME: make private
    static void buildGraph(final Graph<Block, ConditionalRule> graph, final Set<ConditionalRule> rules) {
        for (final ConditionalRule rule : rules) {
            final Block start = new Block((rule.getLeft()).getRootSymbol());
            final Block end = new Block(((TRSFunctionApplication) rule.getRight()).getRootSymbol());
            Node<Block> startNode = graph.getNodeFromObject(start);
            if (startNode == null) {
                startNode = new Node<Block>(start);
            }
            Node<Block> endNode = graph.getNodeFromObject(end);
            if (endNode == null) {
                endNode = new Node<Block>(end);
            }
            graph.addEdge(startNode, endNode, rule);
        }
    }

    /**
     * Iff <code>restoreVarCondition</code> is set, remove conditions which
     * contain variables which do not occur on the lhs.
     */
    private ImmutableList<Condition> filterCond(
        final TRSFunctionApplication lhs,
        final TRSFunctionApplication rhs,
        final ImmutableList<Condition> conds)
    {
        if (!this.restoreVarCondition) {
            return conds;
        }

        final List<Condition> newConds = new ArrayList<Condition>(conds.size());
        final Set<TRSVariable> vars = lhs.getVariables();

        for (final Condition cond : conds) {
            if (vars.containsAll(cond.getVariables())) {
                newConds.add(cond);
            } else {
                /* XXX: We might be able to implement something more intelligent here,
                   but for the moment just drop these conditions */
                if (Globals.DEBUG_NOSCHINSKI) {
                    CLSSlicingProcessor.LOG.finest("Dropped condition "
                        + cond
                        + " because variable condition was not satisfied in "
                        + Rule.create(lhs, rhs));
                }
            }
        }

        return ImmutableCreator.create(newConds);
    }

    private static class CLSArguments {
        public Set<ConditionalRule> rules;
        public Set<TRSFunctionApplication> initialTerms;

        public CLSArguments(final Set<ConditionalRule> rules, final Set<TRSFunctionApplication> initialTerms) {
            this.rules = rules;
            this.initialTerms = initialTerms;
        }
    }

    // FIXME make private
    static class Block {
        private final FunctionSymbol blockSymbol;
        private final boolean needed[];

        public Block(final FunctionSymbol blockSymbol) {
            this.blockSymbol = blockSymbol;
            this.needed = new boolean[blockSymbol.getArity()];
        }

        public boolean[] getNeeded() {
            return this.needed;
        }

        public boolean getNeeded(final int i) {
            return this.needed[i];
        }

        public boolean setNeeded(final int i) {
            if (this.needed[i]) {
                return false;
            }
            this.needed[i] = true;
            return true;
        }

        @Override
        public boolean equals(final Object o) {
            if (!(o instanceof Block)) {
                return false;
            }
            final Block other = (Block) o;
            return this.blockSymbol.equals(other.blockSymbol);
        }

        @Override
        public int hashCode() {
            return this.blockSymbol.hashCode();
        }

        @Override
        public String toString() {
            final StringBuilder sb = new StringBuilder();
            sb.append(this.blockSymbol);
            sb.append(" # ");
            for (final boolean element : this.needed) {
                sb.append(element ? "X" : "o");
            }
            return sb.toString();
        }

        public FunctionSymbol getBlockSymbol() {
            return this.blockSymbol;
        }
    }

    public class CLSSlicingProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Sliced variables";
        }

    }

    public static class Arguments {
        public boolean restoreVarCondition = true;
        public boolean SCCs = false;
    }

}
