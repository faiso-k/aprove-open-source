package aprove.input.Programs.llvm.processors;

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


public class LLVMSEGraphToIntTRSProcessor extends LLVMGraphToIntTRSProcessor {

    @ParamsViaArgumentObject
    public LLVMSEGraphToIntTRSProcessor(Arguments arguments) {
        super(arguments);
    }

    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        
        YNMImplication implication = YNMImplication.EQUIVALENT;
        if (containsOverapproximation(obl, aborter)) {
            implication = YNMImplication.SOUND;
        }
        
        return process(obl, oblNode, aborter, rti, implication);
    }

    private boolean containsOverapproximation(BasicObligation problem, Abortion aborter) {
        for (Node<LLVMAbstractState> node : getNodes(problem)) {
            if (node.getObject().isOverapproximation(aborter)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof LLVMSEGraphProblem);
    }

    @Override
    public Set<Node<LLVMAbstractState>> getNodes(BasicObligation problem) {
        if (Globals.useAssertions) {
            assert problem instanceof LLVMSEGraphProblem;
        }
        LLVMSEGraphProblem graphProblem = (LLVMSEGraphProblem)problem;
        
        return graphProblem.getGraph().getNodes();
    }

    @Override
    public Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> getEdges(BasicObligation problem) {
        if (Globals.useAssertions) {
            assert problem instanceof LLVMSEGraphProblem;
        }
        LLVMSEGraphProblem graphProblem = (LLVMSEGraphProblem)problem;
        
        return graphProblem.getGraph().getEdges();
    }

    @Override
    public Node<LLVMAbstractState> getStartNode(BasicObligation problem) {
        if (Globals.useAssertions) {
            assert problem instanceof LLVMSEGraphProblem;
        }
        LLVMSEGraphProblem graphProblem = (LLVMSEGraphProblem)problem;
        
        return graphProblem.getGraph().getRoot();
    }

    @Override
    public Proof createProof(List<Pair<String, ? extends RuleSet>> conversionLog) {
        return new SEGraphToIRSProof(conversionLog);
    }
    
    public class SEGraphToIRSProof extends LLVMGraphToRulesProof {

        /**
         * Create the proof.
         * @param l Documentation about the magic we've done in the conversion.
         */
        public SEGraphToIRSProof(List<Pair<String, ? extends RuleSet>> l) {
            super(l, "SEGraph to IRS", "LLVM SE-graph to IRS Proof");
        }

    }


}
