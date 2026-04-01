package aprove.verification.oldframework.IRSwT.Utils;

import java.io.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class IRSwTOutput {
    /**
     * Writes the given problem to a file at the given path. If the file already
     * exists, it is overwritten. If the file does not already exist, it is
     * created.
     *
     * @param path
     *            Some path. Must not be null. Must point to a (possibly
     *            non-existing) file in an existing folder.
     * @param problem
     *            The problem to write to the file. Must not be null. May be empty.
     */
    public void dumpIRSwT(String path, IRSwTProblem problem) {
        try {
            FileWriter writer = new FileWriter(path);
            writer.write(problem.toString());
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * The dependency graph of a IRSwTProblem is defined as the graph containing
     * all outermost function symbols appearing in the rules as nodes. Two nodes
     * f and g are connected if there is a rule f(...) -> g(...) is in the
     * problem.
     *
     * @param path
     *            Some path. Must not be null. Must point to a (possibly
     *            non-existing) file in an existing folder.
     * @param problem
     *            The problem for which to create and dump the dependency graph
     *            to the file. Must not be null. May be empty.
     */
    public void dumpDependencyGraph(String path, IRSwTProblem problem) {
        final SimpleGraph<FunctionSymbol, IGeneralizedRule> problemGraph = new SimpleGraph<>();
        final Map<FunctionSymbol, Node<FunctionSymbol>> nodes = new HashMap<>();
        for(IGeneralizedRule rule : problem.getRules()){
            final FunctionSymbol lhsFuncSymb = rule.getLeft().getRootSymbol();
            if(!nodes.containsKey(lhsFuncSymb)) {
                nodes.put(lhsFuncSymb, new Node<>(lhsFuncSymb));
            }
            final Node<FunctionSymbol> lhsNode = nodes.get(lhsFuncSymb);

            final FunctionSymbol rhsFuncSymb = ((TRSFunctionApplication)rule.getRight()).getRootSymbol();
            if(!nodes.containsKey(rhsFuncSymb)) {
                nodes.put(rhsFuncSymb, new Node<>(rhsFuncSymb));
            }
            final Node<FunctionSymbol> rhsNode = nodes.get(rhsFuncSymb);
            problemGraph.addEdge(lhsNode, rhsNode, rule);
        }

        try {
            FileWriter writer = new FileWriter(path);
            writer.write(problemGraph.toSaveDOTwithEdges());
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}
