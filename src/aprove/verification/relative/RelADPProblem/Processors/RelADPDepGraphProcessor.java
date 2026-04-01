package aprove.verification.relative.RelADPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.relative.RelADPProblem.*;

/**
 * Dependency Graph Processor as described in [IJCAR24]
 * 
 * @author Grigory Vartanyan, Jan-Christoph Kassing
 * @version $Id$
 */
public class RelADPDepGraphProcessor extends RelADPProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isRelADPPApplicable(final RelADPProblem reladpp) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processRelADPProblem(final RelADPProblem origreladpp, final Abortion aborter) throws AbortionException {
        final RelDepGraph depGraph = origreladpp.getRelDepGraph();
        final Graph<Rule, ?> graph = depGraph.getGraph();

        final List<RelADPProblem> newProblems = new ArrayList<>();

        int[] stats = {0, 0};
        /*
         * 0: # of SCCs with nodes from P_abs
         * 1: # of Lassos
         */
        
        // SCCs of dependency graph
        final Set<Cycle<Rule>> sccs = depGraph.getGraph().getSCCs(true);
        // dependency graph only marked nodes
        Graph<Rule, ?> graphOnlyMarkedNodes = depGraph.getGraph().getCopy();
        Set<Node<Rule>> nodesToRemove = new HashSet<>();
        for(Node<Rule> node : graphOnlyMarkedNodes.getNodes()) {
            if(!origreladpp.isMarked(node.getObject())) {
                nodesToRemove.add(node);
            }
        }
        for(Node<Rule> node : nodesToRemove) {
            graphOnlyMarkedNodes.removeNode(node);
        }
        // SCCs of dependency graph with only marked nodes
        final Set<Cycle<Rule>> sccsOnlyMarkedGraph = graphOnlyMarkedNodes.getSCCs(true);

        // Check if the SCC contains a rule from P_abs, 
        // then add a corresponding subproblem for the SCC
        sccLoop: for (Cycle<Rule> scc : sccs) {
            for (Node<Rule> node : scc) {
                Rule rule = node.getObject();
                if (!origreladpp.isMarked(rule)) {
                    var subProblem = extract_nodeset(scc.getNodeObjects(), origreladpp, false);
                    newProblems.add(subProblem);
                    stats[0] += 1;
                    continue sccLoop;
                }
            }
        }

        // Check if the SCC contains a node with two annotations, 
        // then add a corresponding subproblem for the lasso
        sccLoop: for (Cycle<Rule> scc : sccsOnlyMarkedGraph) {
            for (Node<Rule> node : scc) {
                Rule rule = node.getObject();
                if (rule.getRight().countAnnos(origreladpp.getDeannotator().keySet()) >= 2) {
                    // Do DFS to find a path to a node from P_abs
                    Set<RelADPProblem> foundPathProblems = dfsSearcher(scc.getNodeObjects(), scc.getNodeObjects(), origreladpp);
                    if(foundPathProblems == null) { //Found a Lasso that covers the whole graph
                        return ResultFactory.unsuccessful();
                    }
                    stats[1] += foundPathProblems.size();
                    newProblems.addAll(foundPathProblems);
                    continue sccLoop;
                }
            }
        }

        RelADPDepGraphProof DGPproof = new RelADPDepGraphProof(depGraph, stats, origreladpp, newProblems);

        for(RelADPProblem newProblem : newProblems) {
            if(newProblem.countAnnoInRHS() == origreladpp.countAnnoInRHS()) {
                return ResultFactory.unsuccessful();
            }
        }
        
        final Result result = ResultFactory.provedAnd(newProblems, YNMImplication.EQUIVALENT, DGPproof);
        return result;

    }

    private RelADPProblem extract_nodeset(Set<Rule> nodes, RelADPProblem problem, boolean unmark) {
        Set<Rule> newPAbs = new HashSet<>();
        Set<Rule> newPRel = new HashSet<>();
        for(Rule rule : problem.getPAbs()) {
            if(nodes.contains(rule)) {
                newPAbs.add(rule);
            } else {
                if(rule.getRight() instanceof TRSFunctionApplication) {
                    TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
                    Rule disAnnoRule = Rule.create(rule.getLeft(), rhs.renameAtAllMap(rule.getRight().getPositions(), problem.getDeannotator()));
                    newPRel.add(disAnnoRule);
                } else {
                    newPRel.add(rule);
                }
            }
        }
        
        for(Rule rule : problem.getPRel()) {
            if(nodes.contains(rule)) {
                newPRel.add(rule);
            } else {
                if(rule.getRight() instanceof TRSFunctionApplication) {
                    TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
                    Rule disAnnoRule = Rule.create(rule.getLeft(), rhs.renameAtAllMap(rule.getRight().getPositions(), problem.getDeannotator()));
                    newPRel.add(disAnnoRule);
                } else {
                    newPRel.add(rule);
                }
            }
        }
        
        final RelADPProblem newProblem = RelADPProblem.create(newPAbs, newPRel, problem.getQ(), problem.getBiAnnoMap());

        return newProblem;
    }

    private Set<RelADPProblem> dfsSearcher(
        Set<Rule> originSCC,
        Set<Rule> avoidSCC,
        RelADPProblem problem
    ) {
        Graph<Rule, ?> graph = problem.getRelDepGraph().getGraph();
        Set<ArrayList<Rule>> pathes = new HashSet<ArrayList<Rule>>();
        for (Rule startNode : originSCC) {
//            Set<Rule> visited = new HashSet<Rule>(graph.getNodes().size());  // TODO: linear search for now
            ArrayList<Rule> path = new ArrayList<Rule>(graph.getNodes().size());
            path.add(startNode);
            dfsSearcherRec(problem, path, pathes, avoidSCC);  // Side effect: adds stuff to res
        }

        int problemSize = problem.getPAbs().size() + problem.getPRel().size();

        Set<RelADPProblem> res = new HashSet<RelADPProblem>(pathes.size());
        for (ArrayList<Rule> path : pathes) {
            Set<Rule> nodes = new HashSet<Rule>(originSCC);
            nodes.addAll(path);

            if (nodes.size() == problemSize) {
                // Found a path that covers the whole graph
                // So the proc was not actually applicable
//                problem.getRelDepGraph().setAtomic();
                return null;
            }

//            System.out.println("   Found Path:");
//            for (Rule node : path) {
//                System.out.println("    " + node.toString());
//            }
            
            RelADPProblem newProblem = extract_nodeset(nodes, problem, false);
            res.add(newProblem);
        }
        return res;
    }

    private void dfsSearcherRec(
        RelADPProblem problem,
        ArrayList<Rule> cur_path,
        Set<ArrayList<Rule>> res,
        Set<Rule> avoidSCC
    ) {
        Graph<Rule, ?> graph = problem.getRelDepGraph().getGraph();
        Rule curPos = cur_path.get(cur_path.size() - 1);  // cur_path cannot (should never) be empty
        Node<Rule> curPosNode = graph.getNodeFromObject(curPos);  // cur_path cannot (should never) be empty
        for (Node<Rule> childNode : graph.getOut(curPosNode)) {
            Rule child = childNode.getObject();
            if (avoidSCC.contains(child)) {
                continue;
            }
            if (cur_path.contains(child)) {  // TODO: avoid linear search later
                continue;
            }

            cur_path.add(child);  // So the child is important. Push it in.

            if (!problem.isMarked(child)) {  // success! found unmarked node, save the path and destory the child
                ArrayList<Rule> new_path = new ArrayList<Rule>(cur_path.subList(1, cur_path.size()));
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

    public static class RelADPDepGraphProof extends RelADPProof implements DOT_Able {

        private final RelDepGraph graph;
        private final int[] stats;
        private final RelADPProblem origObl;
        private final List<RelADPProblem> resultObls;

        private RelADPDepGraphProof(final RelDepGraph graph, final int[] stats,
                final RelADPProblem origObl, final List<RelADPProblem> resultObls) {
            this.graph = graph;
            this.stats = stats;
            this.origObl = origObl;
            this.resultObls = resultObls;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String res = "";
            res += o.paragraph();
            res += "We use the relative dependency graph processor " + o.cite(Citation.IJCAR24) + ".";
            res += o.linebreak();
            res += "The approximation of the Relative Dependency Graph contains:";
            res += o.linebreak();
            res += "  " + this.stats[0] + " SCC" + ((this.stats[0] == 1) ? "" : "s") + " with nodes from P_abs" + ",";
            res += o.linebreak();
            res += "  " + this.stats[1] + " Lasso" + ((this.stats[1] == 1) ? "" : "s") + ",";
            res += o.linebreak();
            res += "Result: This relative DT problem is equivalent to " + (this.stats[0] + this.stats[1]);
            res += " subproblem" + (((this.stats[0] + this.stats[1]) == 1) ? "" : "s") + ".";
            res += o.cond_linebreak();

            return o.export(res);
        }

        @Override
        public String toDOT() {
            return this.graph.toDOT();
        }

    }

}
