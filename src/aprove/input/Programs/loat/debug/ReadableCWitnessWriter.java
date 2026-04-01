package aprove.input.Programs.loat.debug;

import java.util.*;

import aprove.input.Programs.llvm.utils.*;

public class ReadableCWitnessWriter {

    public static void writeCWitness(List<CState> tail, List<CState> loop) {
        StringBuilder sb = new StringBuilder();

        sb.append("**TAIL:**\n\n");
        for (CState t : tail) {
            sb.append(t.getCLine()+": "+t.getSourceCode()+"\n");
        }
        sb.append("\n**LOOP:**\n\n");
        for (CState l : loop) {
            sb.append(l.getCLine()+": "+l.getSourceCode()+"\n");
        }
        
        FileWriter.dumpString(sb.toString(), "cWitness.txt");
    }
    
}
