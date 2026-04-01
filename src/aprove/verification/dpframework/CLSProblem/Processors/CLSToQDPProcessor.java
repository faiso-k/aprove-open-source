package aprove.verification.dpframework.CLSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CLSProblem.*;
import aprove.verification.dpframework.CLSProblem.Processors.CLSSlicingProcessor.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

// XXX: This processor still includes a slicing pass and it seems a dependency graph processor.
// Is it necessary to do the dpgraph inside this processor? Or can we remove all this graph stuff
// by using a CLSSlicingProcessor before and a DPGraphProcessor afterwards?
@NoParams
public class CLSToQDPProcessor extends CLSProcessor {

    @Override
    public boolean isCLSApplicable(final CLSProblem obl) {
        return true;
    }

    @Override
    protected Result processCLS(final CLSProblem problem, final Abortion aborter) throws AbortionException {
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
        final Set<QDPProblem> qdps = new LinkedHashSet<QDPProblem>();
        for (final Cycle<Block> cycle : graph.getSCCs()) {
            final Graph<Block, ConditionalRule> scc = graph.getSubGraph(cycle);
            while (true) {
                final boolean changed = CLSSlicingProcessor.propagateGraph(scc);
                if (!changed) {
                    break;
                }
            }
            final Set<Rule> newRules = new LinkedHashSet<Rule>();
            final Set<ConditionalRule> newCondRules = new LinkedHashSet<ConditionalRule>();
            final Set<Rule> builtInRules = new LinkedHashSet<Rule>();
            CLSToQDPProcessor.oldExtractRules(scc, newRules, newCondRules, builtInRules);
            final Set<Rule> allRules = new LinkedHashSet<Rule>(newRules.size() + builtInRules.size());
            allRules.addAll(newRules);
            allRules.addAll(builtInRules);
            final CTRSProblem ctrs =
                CTRSProblem.create(ImmutableCreator.create(allRules), ImmutableCreator.create(newCondRules));
            final FreshNameGenerator fg = ctrs.getFreshNameGenerator();
            final Map<ConditionalRule, List<Rule>> mapping = new HashMap<>();
            final Set<Rule> P = CTRSToQTRSProcessor.translate(ctrs.getC(), fg, true, true, mapping);
            P.addAll(newRules);
            final QTermSet Q = new QTermSet(CollectionUtils.getLeftHandSides(builtInRules));
            final QTRSProblem qtrs = QTRSProblem.create(ImmutableCreator.create(builtInRules), Q);
            final QDPProblem qdp = QDPProblem.create(P, qtrs, true);
            qdps.add(qdp);
        }
        return ResultFactory.provedAnd(qdps, YNMImplication.SOUND, new CLSToQDPProof());
    }

    @Deprecated
    private static void oldExtractRules(
        final Graph<Block, ConditionalRule> graph,
        final Set<Rule> newRules,
        final Set<ConditionalRule> newCondRules,
        final Set<Rule> builtInRules)
    {
        final Afs afs = new Afs();
        for (final Node<Block> node : graph.getNodes()) {
            final Block block = node.getObject();
            afs.setFiltering(block.getBlockSymbol(), block.getNeeded());
        }
        final Map<FunctionSymbol, FunctionSymbol> predefs = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
        for (final Edge<ConditionalRule, Block> edge : graph.getEdges()) {
            final ConditionalRule rule = edge.getObject();
            final TRSFunctionApplication newLeft =
                (TRSFunctionApplication) CLSToCTRSProcessor.extractTerm(
                    afs.filterTerm(rule.getLeft()),
                    predefs,
                    builtInRules);
            final TRSFunctionApplication newRight =
                (TRSFunctionApplication) CLSToCTRSProcessor.extractTerm(
                    afs.filterTerm(rule.getRight()),
                    predefs,
                    builtInRules);
            final ImmutableList<Condition> conds = rule.getConditions();
            final List<Condition> newConds = new ArrayList<Condition>(conds.size());
            for (final Condition cond : conds) {
                final Condition newCond =
                    Condition.create(
                        CLSToCTRSProcessor.extractTerm(cond.getLeft(), predefs, builtInRules),
                        CLSToCTRSProcessor.extractTerm(cond.getRight(), predefs, builtInRules),
                        cond.getType());
                newConds.add(newCond);
            }
            final Rule newRule = Rule.create(newLeft, newRight);
            if (newConds.isEmpty()) {
                newRules.add(newRule);
            } else {
                newCondRules.add(ConditionalRule.create(newRule, ImmutableCreator.create(newConds)));
            }
        }
    }

    public class CLSToQDPProof extends DefaultProof {

        public CLSToQDPProof() {
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Sliced variables and converted to QDPProblems";
        }

    }

}
