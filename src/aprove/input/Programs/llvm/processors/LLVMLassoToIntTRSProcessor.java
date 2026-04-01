package aprove.input.Programs.llvm.processors;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class LLVMLassoToIntTRSProcessor extends LLVMGraphToIntTRSProcessor {
    
    /**
     * @param arguments The parameters of this processor.
     */
    @ParamsViaArgumentObject
    public LLVMLassoToIntTRSProcessor(Arguments arguments) {
        super(arguments);
    }
    
    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof LLVMLassoProblem);
    }
    
    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) {
        if (Globals.useAssertions) {
            assert obl instanceof LLVMLassoProblem;
        }
        
        LLVMLassoProblem problem = (LLVMLassoProblem)obl;
        
        YNMImplication implication = YNMImplication.EQUIVALENT;
        if (containsOverapproximation(problem, aborter)) {
            implication = YNMImplication.SOUND;
        }
        
        return super.process(obl, oblNode, aborter, rti, implication);
    }
    
    private boolean containsOverapproximation(LLVMSCCProblem problem, Abortion aborter) {
        for (Node<LLVMAbstractState> node : getNodes(problem)) {
            if (node.getObject().isOverapproximation(aborter)) {
                return true;
            }
        }
        return false;
    }
    
    @Override
    public Set<Node<LLVMAbstractState>> getNodes(BasicObligation problem) {
        if (Globals.useAssertions) {
            assert problem instanceof LLVMLassoProblem; 
        }
        LLVMLassoProblem lassoProblem = (LLVMLassoProblem)problem;
        
        Set<Node<LLVMAbstractState>> nodes = new LinkedHashSet<>(lassoProblem.getSCC().getNodes());
        
        List<Edge<LLVMEdgeInformation, LLVMAbstractState>> tail = lassoProblem.getTail();
        

        for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge: tail) {
            nodes.add(edge.getStartNode());
            nodes.add(edge.getEndNode());
        }
        return nodes;
    }
    
    @Override
    public Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> getEdges(BasicObligation problem) {
        if (Globals.useAssertions) {
            assert problem instanceof LLVMLassoProblem; 
        }
        LLVMLassoProblem lassoProblem = (LLVMLassoProblem)problem;
        
        Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> edges = new LinkedHashSet<>(lassoProblem.getSCC().getEdges());
        
        if (Globals.useAssertions) {
            assert problem instanceof LLVMLassoProblem; 
        }
        edges.addAll(lassoProblem.getTail());

        return edges;
    }
    
    @Override
    public Node<LLVMAbstractState> getStartNode(BasicObligation problem) {
        if (Globals.useAssertions) {
            assert problem instanceof LLVMLassoProblem; 
        }
        LLVMLassoProblem lassoProblem = (LLVMLassoProblem)problem;
        
        List<Edge<LLVMEdgeInformation, LLVMAbstractState>> tail = lassoProblem.getTail();

        if (tail.size() >= 1) {
            return tail.get(0).getStartNode();
        } else {
            return null;
        }
    }

    @Override
    public Proof createProof(List<Pair<String, ? extends RuleSet>> conversionLog) {
        return new LassoToIRSProof(conversionLog);
    }
    
    public class LassoToIRSProof extends LLVMGraphToRulesProof {

        /**
         * Create the proof.
         * @param l Documentation about the magic we've done in the conversion.
         */
        public LassoToIRSProof(List<Pair<String, ? extends RuleSet>> l) {
            super(l, "Lasso2IRS", "LLVM Lasso to IRS Proof");
        }

    }
}
