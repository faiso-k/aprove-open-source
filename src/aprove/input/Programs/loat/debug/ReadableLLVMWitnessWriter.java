package aprove.input.Programs.loat.debug;

import java.util.*;

import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class ReadableLLVMWitnessWriter {
    
    public static void writeLLVMWitness(List<Node<LLVMAbstractState>> tail, List<Node<LLVMAbstractState>> loop) {
        StringBuilder sb = new StringBuilder();
        sb.append("**TAIL:**\n\n");
        for (Node<LLVMAbstractState> t : tail) {
            sb.append(t.getObject().getProgramPosition().toString()+": "+t.getObject().getCurrentInstruction().toString()+"\n");
        }
        sb.append("\n**LOOP:**\n\n");
        for (Node<LLVMAbstractState> l : loop) {
            sb.append(l.getObject().getProgramPosition().toString()+": "+l.getObject().getCurrentInstruction().toString()+"\n");
        }
        
        FileWriter.dumpString(sb.toString(), "llvmWitness.txt");
    }
    
}
