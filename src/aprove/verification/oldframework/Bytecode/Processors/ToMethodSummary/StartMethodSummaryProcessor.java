package aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Obligations.Junctors.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary.MethodSummaryBuilder.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.*;

public class StartMethodSummaryProcessor extends Processor.ProcessorSkeleton {

    public static class Arguments {
        public String filename;
    }

    private Arguments arguments;

    @ParamsViaArgumentObject
    public StartMethodSummaryProcessor(Arguments arguments) {
        this.arguments = arguments;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        TerminationGraph terminationGraph = ((JBCTerminationGraphProblem) obl).getGraph();

        /*
         * Merge method graphs into one graph, make call/return edges
         * explicit. We then search for the SCCs and encode these as
         * separate problems to IDP. For each node, note in which method
         * graph it is.
         */
        final Map<Node, MethodGraph> nodeToMethodGraphMap = new LinkedHashMap<>();
        final Map<Node, Node> oldNodeToNewNodeMap = new LinkedHashMap<>();

        final JBCGraph termGraph =
            TerminationGraphToSingleGraph.createSingleGraph(terminationGraph, nodeToMethodGraphMap, oldNodeToNewNodeMap);


        //store class & method name etc.
        IMethod method = terminationGraph.getStartGraph().getStartNode().getState().getCurrentStackFrame().getMethod();

        //find all changed local variables using input references
        Set<Integer> changedLocVars = new LinkedHashSet<>();
        //first find return states
        for (Node node : termGraph.getNodes()) {
            if (node.getState().callStackEmpty()) { //we found a return state
                for (Edge inEdge : node.getInEdges()) { //get to the previous state in the graph
                    StackFrame frame = inEdge.getStart().getState().getCurrentStackFrame();
                    assert frame.getMethod().equals(method);
                    for (RootInputReference ir : frame.getInputReferences().getRootInputReferences()) { //add all changed IRs
                        if (ir.getChanged() && ir.getPosition() instanceof LocVarRootPosition) {
                               changedLocVars.add(((LocVarRootPosition)ir.getPosition()).getVarIndex());
                        }
                    }
                }
            }
        }

        //check if env got changed
        boolean changedEnv = false;
        outer: for (Edge edge : termGraph.getEdges()) {
            if (edge.getLabel() instanceof PredefinedMethodEdge) {
                PredefinedMethodEdge pme = (PredefinedMethodEdge) edge.getLabel();
                for (VariableInformation vi : pme) {
                    if (vi instanceof EnvrionmentChangeInformation) {
                        changedEnv = true;
                        break outer;
                    }
                }
            }
        }

        //create result
        MethodSummaryBuilder summaryBuilder = new MethodSummaryBuilder(method, changedLocVars, changedEnv, arguments.filename);
        List<MethodSummaryBuilder.Task> tasks = summaryBuilder.getTasks();
        List<TerminationGraphForMethodSummary> newObls = new ArrayList<>(tasks.size());
        for (MethodSummaryBuilder.Task task : tasks) {
            newObls.add(new TerminationGraphForMethodSummary(terminationGraph, task));
        }

        //no lower-bound analysis implemented yet, default them to best case
        summaryBuilder.setLowerTime(SimplePolynomial.ZERO);
        summaryBuilder.setLowerSpace(SimplePolynomial.ZERO);

        return ResultFactory.provedWithJunctor(newObls, Junctors.BEST, BothBounds.create(), new CreateMethodSummaryProof(tasks));
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof JBCTerminationGraphProblem;
    }

    public class CreateMethodSummaryProof extends DefaultProof {

        private List<MethodSummaryBuilder.Task> tasks;

        public CreateMethodSummaryProof(List<Task> tasks) {
            this.tasks = new ArrayList<>(tasks);
        }

        /**
         * @param o export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "writing method summary to " + arguments.filename + o.newline() + "generated Tasks: " + tasks;
        }
    }


}
