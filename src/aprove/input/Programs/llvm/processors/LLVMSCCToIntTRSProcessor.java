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


public class LLVMSCCToIntTRSProcessor extends LLVMGraphToIntTRSProcessor {

    @ParamsViaArgumentObject
    public LLVMSCCToIntTRSProcessor(Arguments arguments) {
        super(arguments);
    }
    
    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof LLVMSCCProblem);
    }

    /**
     * Work on the given obligation.
     * @param obl a TerminationGraphProblem
     * @param oblNode ignored.
     * @param aborter some aborter
     * @param rti ignored.
     * @return one obligation per SCC
     */
    @Override
    public Result process(
        BasicObligation obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
    ) {
        return process(obl, oblNode, aborter, rti, YNMImplication.SOUND);
    }
    
    public Set<Node<LLVMAbstractState>> getNodes(BasicObligation problem) {
        if (Globals.useAssertions) {
            assert problem instanceof LLVMSCCProblem;
        }
        return ((LLVMSCCProblem)problem).getSCC().getNodes();
    }
    
    public Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> getEdges(BasicObligation problem) {
        if (Globals.useAssertions) {
            assert problem instanceof LLVMSCCProblem;
        }
        return ((LLVMSCCProblem)problem).getSCC().getEdges();
    }
    
    public Node<LLVMAbstractState> getStartNode(BasicObligation problem) {
        return null;
    }
    
    @Override
    public Proof createProof(List<Pair<String, ? extends RuleSet>> conversionLog) {
        return new SCCToIRSProof(conversionLog);
    }
    
    /**
     * A very fine proof.
     * @author Marc Brockschmidt
     */
    public class SCCToIRSProof extends LLVMGraphToRulesProof {

        /**
         * Create the proof.
         * @param l Documentation about the magic we've done in the conversion.
         */
        public SCCToIRSProof(List<Pair<String, ? extends RuleSet>> l) {
            super(l, "SCC2IRS", "LLVM SCC to IRS Proof");
        }

    }
}
