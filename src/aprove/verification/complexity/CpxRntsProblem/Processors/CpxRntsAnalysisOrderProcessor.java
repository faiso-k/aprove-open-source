package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import aprove.Globals;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Analysis Order processor for RntsProblem
 *
 * Uses SCC decomposition to establish an order in which the function symbols
 * can be analyzed. If no ordering is found (in case of nested mutual recursion)
 * returns unsuccessful.
 *
 * @author mnaaf
 *
 */
public class CpxRntsAnalysisOrderProcessor extends ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (!(obl instanceof CpxRntsProblem)) {
            return false;
        }
        CpxRntsProblem rnts = (CpxRntsProblem)obl;
        return !rnts.hasAnalysisOrder();
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        CpxRntsAnalysisOrderWorker worker = new CpxRntsAnalysisOrderWorker();
        Result res = worker.process(obl, oblNode, aborter, rti);
        return res;
    }

    /**
     * Helper class to encapsulate the instance-dependent state of the
     * computation by the processor.
     */
    private static class CpxRntsAnalysisOrderWorker {
        private Graph<FunctionSymbol, RntsRule> graph = null;
        private Set<FunctionSymbol> rhsSyms = null;

        //builds this.graph and sets this.rhsSyms
        private void setupGraph(CpxRntsProblem rnts) {
            this.graph = new Graph<>();

            //collect all relevant symbols
            HashSet<FunctionSymbol> allSyms = new HashSet<FunctionSymbol>();
            HashSet<FunctionSymbol> rhsSyms = new HashSet<FunctionSymbol>();
            for (RntsRule rule : rnts.getRules()) {
                allSyms.add(rule.getRootSymbol());
                rhsSyms.addAll(rule.getRight().getFunctionSymbols());
            }
            allSyms.addAll(rhsSyms);
            this.rhsSyms = rhsSyms;

            //create nodes for all occurring function symbols
            for (FunctionSymbol sym : allSyms) {
                if (!rnts.isDefinedSymbol(sym)) continue;
                graph.addNode(new Node<FunctionSymbol>(sym));
            }

            //add edge f -> g for all rules f -> * where g appears in *
            for (RntsRule rule : rnts.getRules()) {
                Node<FunctionSymbol> src = graph.getNodeFromObject(rule.getRootSymbol());
                for (FunctionSymbol dst : rule.getRight().getFunctionSymbols()) {
                    if (!rnts.isDefinedSymbol(dst)) continue;
                    graph.addEdge(src, graph.getNodeFromObject(dst), rule);
                }
            }
        }

        //checks if multiple functions occur nested on a rhs (this happpens for nested mutual recursion)
        private boolean checkNodesetNesting(Set<FunctionSymbol> nodes, CpxRntsProblem rnts) {
            for (FunctionSymbol fun : nodes) {
                for (RntsRule r : rnts.getRulesFrom(fun)) {
                    if (TermHelper.countFunNesting(r.getRight(), f -> nodes.contains(f)) > 1) {
                        return false;
                    }
                }
            }
            return true;
        }

        public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
                throws AbortionException {
            CpxRntsProblem rnts = (CpxRntsProblem)obl;
            setupGraph(rnts);

            //compute topological order on SCCs
            SCCGraph<FunctionSymbol, RntsRule> sccgraph = new SCCGraph<>(this.graph, false);
            List<Cycle<FunctionSymbol>> scctopo = sccgraph.getRankedSCCs();

            //check if any SCC is nested mutually recursive
            Deque<Set<FunctionSymbol>> order = new LinkedList<>();
            for (Cycle<FunctionSymbol> cycle : scctopo) {
                Set<FunctionSymbol> nodeset = new HashSet<>();
                for (Node<FunctionSymbol> node : cycle) {
                    //all function symbols on this cycle have to be analyzed together
                    //unless they a) are non-initial AND b) not needed for any other symbol (not on any rhs)
                    if (rnts.isInitial(node.getObject()) || this.rhsSyms.contains(node.getObject())) {
                        nodeset.add(node.getObject());
                    }
                }
                if (!checkNodesetNesting(nodeset, rnts)) {
                    if (Globals.DEBUG_MNAAF) {
                        System.err.println("ABORTING: NO ANALYSIS ORDER [nesting]");
                        System.err.println("Within the SCC: " + nodeset);
                    }
                    return ResultFactory.unsuccessful("Nesting within one SCC");
                }
                order.addLast(nodeset);
            }

            CpxRntsProblem newObl = rnts.cloneWithTodo(ImmutableCreator.create(order));
            return ResultFactory.proved(newObl, BothBounds.create(), new CpxRntsAnalysisOrderProof(order));
        }
    }

    private static class CpxRntsAnalysisOrderProof extends CpxProof {
        private final Deque<Set<FunctionSymbol>> order;

        public CpxRntsAnalysisOrderProof(final Deque<Set<FunctionSymbol>> order) {
            this.order = order;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append(o.escape("Found the following analysis order by SCC decomposition:"));
            s.append(o.paragraph());

            StringBuilder orderStr = new StringBuilder();
            for (Set<FunctionSymbol> cycle : order) {
                orderStr.append(o.escape("   ")); //just for plain text output
                orderStr.append(o.escape("{ "));
                orderStr.append(cycle.stream().map(f -> f.export(o)).collect(Collectors.joining(", ")));
                orderStr.append(o.escape(" }"));
                orderStr.append(o.linebreak());
            }
            s.append(o.indent(orderStr.toString()));
            return s.toString();
        }

    }
}
