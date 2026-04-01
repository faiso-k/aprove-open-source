package aprove.verification.oldframework.IRSwT.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import immutables.*;

/*
 * Creates a graph where the defined symbols are the vertices and there is an arc f->g iff
 * there is a rule such that f occurs on the rhs and g occurs on the lhs.
 *
 * Then, it suffices to deal with the SCCs of this graph.
 *
 * This is supposed to be simple and fast.
 *
 * @author ffrohn
 */
public class IRSwTSimpleDependencyGraphProcessor extends Processor.ProcessorSkeleton {

    @Override
    public Result
            process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        IRSwTProblem IRSwT = (IRSwTProblem) obl;
        Set<IGeneralizedRule> rules = IRSwT.getRules();
        SimpleGraph<FunctionSymbol, Void> depGraph = new SimpleGraph<>();
        Map<FunctionSymbol, Node<FunctionSymbol>> nodes = new LinkedHashMap<>();
        // collect the defined symbols and create a node for each one
        for (IGeneralizedRule r: rules) {
            FunctionSymbol f = r.getRootSymbol();
            if (!nodes.containsKey(f)) {
                Node<FunctionSymbol> node = new Node<>(f);
                nodes.put(f, node);
                depGraph.addNode(node);
            }
        }
        // add the edges to the graph
        for (IGeneralizedRule r: rules) {
            for (FunctionSymbol f: r.getLeft().getFunctionSymbols()) {
                for (FunctionSymbol g: r.getRight().getFunctionSymbols()) {
                    if (nodes.containsKey(f) && nodes.containsKey(g)) {
                        depGraph.addEdge(nodes.get(f), nodes.get(g));
                    }
                }
            }
        }
        // create a new problem for each SCC
        LinkedHashSet<Cycle<FunctionSymbol>> sccs = depGraph.getSCCs(true);
        Set<IRSwTProblem> newIRSwTs = new LinkedHashSet<>();

        final Node<FunctionSymbol> rootNode;
        if(IRSwT.getStartTerm() == null) {
            rootNode = null;
        } else {
            rootNode = nodes.get(IRSwT.getStartTerm().getRootSymbol());
        }
        sccs = this.removeUnreachableSccs(rootNode, depGraph, sccs);
        for (Cycle<FunctionSymbol> anScc: sccs) {
            Set<IGeneralizedRule> newRules = new LinkedHashSet<>();
            for (IGeneralizedRule r: rules) {
                Set<FunctionSymbol> intersection = new LinkedHashSet<>();
                intersection.addAll(anScc.getNodeObjects());
                intersection.retainAll(r.getLeft().getFunctionSymbols());
                if (!intersection.isEmpty()) {
                    intersection.clear();
                    intersection.addAll(anScc.getNodeObjects());
                    intersection.retainAll(r.getRight().getFunctionSymbols());
                    if (!intersection.isEmpty()) {
                        newRules.add(r);
                    }
                }
            }
            if (newRules.equals(rules)) {
                return ResultFactory.unsuccessful();
            }
            IRSwTProblem aNewIRSwT = new IRSwTProblem(ImmutableCreator.create(newRules));
            newIRSwTs.add(aNewIRSwT);
        }

        return ResultFactory.provedAnd(newIRSwTs, YNMImplication.EQUIVALENT, new IRSwTSimpleDependencyGraphProof(newIRSwTs));
    }

    /**
     * A scc is reachable if there is a path from the node of the root symbol of
     * the start term to some node in the scc. If there is no root node, then all
     * sccs have to be considered reachable.
     *
     * @param rootNode
     *            The starting node of the given dependency graph. May be null.
     * @param depGraph
     *            A graph where f -> g iff there is a rule f(...) -> g(...) in
     *            the given problem
     * @param sccs
     *            The strongly connected components of the given depGraph
     * @return The reachable subset of the given sccs
     */
    private LinkedHashSet<Cycle<FunctionSymbol>> removeUnreachableSccs(
            Node<FunctionSymbol> rootNode,
            SimpleGraph<FunctionSymbol, Void> depGraph,
            LinkedHashSet<Cycle<FunctionSymbol>> sccs) {
        if(rootNode == null) {
            return sccs;
        }

        final LinkedHashSet<Cycle<FunctionSymbol>> returnValue = new LinkedHashSet<>();
        for(Cycle<FunctionSymbol> scc : sccs) {
            final Node<FunctionSymbol> node = scc.iterator().next();
            if(depGraph.hasPath(rootNode, node)) {
                returnValue.add(scc);
            }
        }

        return returnValue;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof IRSwTProblem;
    }

    private class IRSwTSimpleDependencyGraphProof extends Proof {

        private Set<IRSwTProblem> newIRSwTs = new LinkedHashSet<>();

        public IRSwTSimpleDependencyGraphProof(Set<IRSwTProblem> newIRSwTs) {
            this.newIRSwTs.addAll(newIRSwTs);
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            String res = o.export("Constructed simple dependency graph.");
            res += o.newline();
            res += o.export("Simplified to the following IRSwTs:");
            res += o.newline();
            for (IRSwTProblem IRSwT: this.newIRSwTs) {
                res += o.indent(o.export(IRSwT));
                res += o.indent(o.newline());
            }
            return res;
        }

    }

}
