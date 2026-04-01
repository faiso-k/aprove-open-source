package aprove.verification.relative.RDTProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.relative.RDTProblem.*;

/**
 * Dependency Graph Processor as described in G. Vartanyan's bachelor's
 * 
 * @author Grigory Vartanyan
 * @version $Id$
 */
public class RDTDepGraphProcessor extends RDTProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isRDTPApplicable(final RDTProblem rdpp) {
        // if graph is atomic, this is definitely not applicable
        // otherwise, not applicable if graph is a purely (un)marked SCC
        final RelDepGraph graph = rdpp.getDependencyGraph();
        if (graph.isAtomic())
            return false;
        if (graph.isSCC()) {  // FIX ME
            boolean completely_marked = true;
            boolean completely_unmarked = true;
            for (var node : graph.getNodes()) {
                if (rdpp.isMarked(node)) {
                    completely_unmarked = false;
                } else {
                    completely_marked = false;
                }
            }
            if (completely_marked || completely_unmarked)
                return false;
        }
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processRDTProblem(final RDTProblem origrdpp, final Abortion aborter) throws AbortionException {
        final RelDepGraph depGraph = origrdpp.getDependencyGraph();
        final Graph<CoupledPosDepTuple, ?> graph = depGraph.getGraph();

        final List<RDTProblem> newProblems = new ArrayList<>();

        int[] stats = {0, 0, 0, 0, 0, 0};
        /*
         * 0: # of unmarked SCCs
         * 1: # of pseudomarked SCCs
         * 2: # of partially marked SCCs
         * 3: # of purely marked SCCs
         * 4: # of pathes found
         * 5: # of subproblems generated
         */

        final Set<Cycle<CoupledPosDepTuple>> sccs = depGraph.getGraph().getSCCs(true);  // Why re-calculate SCCs here??
        if (depGraph.isSCC()) {  // TODO: what is going on here???
            // Since we already know from the applicability check that isGenuineSCC = false,
            // this means that we have a singleton node (should only occur in certain
            // certification modes).
            return ResultFactory.proved(origrdpp, YNMImplication.EQUIVALENT,
                    new RDTDepGraphProof(depGraph, stats, origrdpp,
                            newProblems));//, new LinkedList<Integer>(), new LinkedList<>(sccs)));
        }

        for (Cycle<CoupledPosDepTuple> scc : sccs) {
//            System.out.println("SCC " + scc.hashCode());
            // Check if unmarked, partially marked or purely marked
            // Might as well calculate the purely marked subSCC while we're at it
            boolean marked = true;
            boolean unmarked = true;
            Cycle<CoupledPosDepTuple> subPureSCC = new Cycle<CoupledPosDepTuple>();
            for (Node<CoupledPosDepTuple> node : scc) {
                CoupledPosDepTuple rule = node.getObject();
//                if (depGraph.isMarked(rule)) {
//                    System.out.print("X ");
//                }
//                System.out.println(rule.toString());
                if (origrdpp.isMarked(rule)) {
                    subPureSCC.add(node);
                    unmarked = false;
                } else {
                    marked = false;
                }
            }

            if (unmarked) {
                // SCC is unmarked.
                // Extract to its own problem and continue to next scc
                var subProblem = extract_nodeset(scc.getNodeObjects(), origrdpp, false);
                newProblems.add(subProblem);
//                System.out.println(" unmarked, moving on");
                stats[0] += 1;
                continue;  // No further processing required
            }

            Set<Cycle<CoupledPosDepTuple>> pureSCCs = graph.getSubGraph(subPureSCC).getSCCs();

            if (!marked && pureSCCs.isEmpty()) {
                // SCC is "pseudomarked". Unmark everything, extract, continue
                var subProblem = extract_nodeset(scc.getNodeObjects(), origrdpp, true);
                newProblems.add(subProblem);
//                System.out.println(" pseudomarked, moving on");
                stats[1] += 1;
                continue;  // No further processing required
            }

            if (!marked) {
                // SCC is NOT pseudomarked, but also not purely marked.
                // extract it to subproblem without unmarking and do DFS
                var subProblem = extract_nodeset(scc.getNodeObjects(), origrdpp, false);
                newProblems.add(subProblem);
//                System.out.println(" partially marked, extracted SCC");
                stats[2] += 1;
            } else {
                stats[3] += 1;
            }

            for (Cycle<CoupledPosDepTuple> pureSCC : pureSCCs) {
                // Do DFS on every pure subSCC
                Set<RDTProblem> foundPathProblems = dfsSearcher(pureSCC.getNodeObjects(), scc.getNodeObjects(), origrdpp);
                if (foundPathProblems == null) {
                    return ResultFactory.notApplicable("Relative Dependency Graph was already atomic");
                }
                stats[4] += foundPathProblems.size();
                newProblems.addAll(foundPathProblems);
            }
        }

        stats[5] = newProblems.size();

//        System.out.println("\n\nFound " + stats[5] + " new problems:");
//        for (RDPProblem prob : newProblems) {
//            for (CoupledPosDepTuple rule : prob.getD2()) {
//                System.out.println("X " + rule.toString());
//            }
//            for (CoupledPosDepTuple rule : prob.getD1()) {
//                System.out.println(rule.toString());
//            }
//            System.out.println("");
//        }

        RDTDepGraphProof DGPproof = new RDTDepGraphProof(depGraph, stats, origrdpp, newProblems);

        final Result result = ResultFactory.provedAnd(newProblems, YNMImplication.EQUIVALENT, DGPproof);
        return result;

    }

    private RDTProblem extract_nodeset(Set<CoupledPosDepTuple> nodes, RDTProblem problem, boolean unmark) {
        // NOTE: the newly created problem is set to be atomic!
        // TODO: add citation/proof thing of minimality of generated subproblems
        final RelDepGraph subGraph = problem.getDependencyGraph().getSubGraph2(nodes);
        subGraph.setAtomic();

        if (unmark) {
            subGraph.unmarkAll();
        }
        
        final RDTProblem newProblem = problem.getSubProblem(subGraph);

        return newProblem;
    }

    private Set<RDTProblem> dfsSearcher(
        Set<CoupledPosDepTuple> originSCC,
        Set<CoupledPosDepTuple> avoidSCC,
        RDTProblem problem
    ) {
        Graph<CoupledPosDepTuple, ?> graph = problem.getDependencyGraph().getGraph();
        Set<ArrayList<CoupledPosDepTuple>> pathes = new HashSet<ArrayList<CoupledPosDepTuple>>();
        for (CoupledPosDepTuple startNode : originSCC) {
//            Set<CoupledPosDepTuple> visited = new HashSet<CoupledPosDepTuple>(graph.getNodes().size());  // TODO: linear search for now
            ArrayList<CoupledPosDepTuple> path = new ArrayList<CoupledPosDepTuple>(graph.getNodes().size());
            path.add(startNode);
            dfsSearcherRec(problem, path, pathes, avoidSCC);  // Side effect: adds stuff to res
        }

        int problemSize = problem.getD1().size() + problem.getD2().size();

        Set<RDTProblem> res = new HashSet<RDTProblem>(pathes.size());
        for (ArrayList<CoupledPosDepTuple> path : pathes) {
            Set<CoupledPosDepTuple> nodes = new HashSet<CoupledPosDepTuple>(originSCC);
            nodes.addAll(path);

            if (nodes.size() == problemSize) {
                // Found a path that covers the whole graph
                // So the proc was not actually applicable
                problem.getDependencyGraph().setAtomic();
                return null;
            }

//            System.out.println("   Found Path:");
//            for (CoupledPosDepTuple node : path) {
//                System.out.println("    " + node.toString());
//            }
            
            RDTProblem newProblem = extract_nodeset(nodes, problem, false);
            res.add(newProblem);
        }
        return res;
    }

    private void dfsSearcherRec(
        RDTProblem problem,
        ArrayList<CoupledPosDepTuple> cur_path,
        Set<ArrayList<CoupledPosDepTuple>> res,
        Set<CoupledPosDepTuple> avoidSCC
    ) {
        Graph<CoupledPosDepTuple, ?> graph = problem.getDependencyGraph().getGraph();
        CoupledPosDepTuple curPos = cur_path.get(cur_path.size() - 1);  // cur_path cannot (should never) be empty
        Node<CoupledPosDepTuple> curPosNode = graph.getNodeFromObject(curPos);  // cur_path cannot (should never) be empty
        for (Node<CoupledPosDepTuple> childNode : graph.getOut(curPosNode)) {
            CoupledPosDepTuple child = childNode.getObject();
            if (avoidSCC.contains(child)) {
                continue;
            }
            if (cur_path.contains(child)) {  // TODO: avoid linear search later
                continue;
            }

            cur_path.add(child);  // So the child is important. Push it in.

            if (!problem.isMarked(child)) {  // success! found unmarked node, save the path and destory the child
                ArrayList<CoupledPosDepTuple> new_path = new ArrayList<CoupledPosDepTuple>(cur_path.subList(1, cur_path.size()));
                res.add(new_path);
            } else {  // the child is marked. Recurse
                dfsSearcherRec(problem, cur_path, res, avoidSCC);
            }

            if (Globals.useAssertions) {  // make sure they didn't swap them in the hospital
                assert cur_path.get(cur_path.size() - 1) == child;
            }
            cur_path.remove(cur_path.size() - 1);  // We've come out of the recursion. Pop child from list.
            // TODO: no tail here, restructure?
        }
    }
    
    // ================================================================================
    // Proof
    // ================================================================================

    public static class RDTDepGraphProof extends RDTProof implements DOT_Able {

        private final RelDepGraph graph;
//        private final int nrSccs;
        private final int[] stats;
//        private final int lessNodes;
        private final RDTProblem origObl;
        private final List<RDTProblem> resultObls;
//        private final LinkedList<Integer> nonSccs;
//        private final Iterable<Cycle<CoupledPosDepTuple>> rankedSccGraph;

        private RDTDepGraphProof(final RelDepGraph graph, final int[] stats,
                final RDTProblem origObl, final List<RDTProblem> resultObls) {
//                final LinkedList<Integer> nonSccs, final Iterable<Cycle<CoupledPosDepTuple>> rankedSccGraph) {
            this.graph = graph;
            this.stats = stats;
//            this.lessNodes = lessNodes;
            this.origObl = origObl;
            this.resultObls = resultObls;
//            this.nonSccs = nonSccs;
//            this.rankedSccGraph = rankedSccGraph;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String res = "";
            res += o.paragraph();
            res += "We use the relative dependency graph processor " + o.cite(Citation.VARTANYAN_BA) + ".";
            res += o.linebreak();
            res += "The approximation of the Relative Dependency Graph contains:";
            res += o.linebreak();
            res += "  " + this.stats[0] + " unmarked SCC" + ((this.stats[0] == 1) ? "" : "s") + ",";
            res += o.linebreak();
            res += "  " + this.stats[1] + " pseudomarked SCC" + ((this.stats[1] == 1) ? "" : "s") + ",";
            res += o.linebreak();
            res += "  " + this.stats[2] + " partially marked SCC" + ((this.stats[2] == 1) ? "" : "s") + " and";
            res += o.linebreak();
            res += "  " + this.stats[3] + " purely marked SCC" + ((this.stats[3] == 1) ? "" : "s") + ".";
            res += o.linebreak();
            res += "From the partially and purely marked SCCs, the processor found " + this.stats[4] + " path";
            res += ((this.stats[4] == 1) ? "" : "es") + " to unmarked nodes.";
            res += o.linebreak();
            res += "Result: this relative DT problem is equivalent to " + this.stats[5];
            res += " subproblem" + ((this.stats[5] == 1) ? "" : "s") + ".";
            res += o.cond_linebreak();

            return o.export(res);
        }

        @Override
        public String toDOT() {
            return this.graph.toDOT();
        }

    }

}
