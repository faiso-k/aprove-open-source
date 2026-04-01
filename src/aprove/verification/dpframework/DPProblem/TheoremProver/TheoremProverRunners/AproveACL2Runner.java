package aprove.verification.dpframework.DPProblem.TheoremProver.TheoremProverRunners;

import java.io.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class AproveACL2Runner implements TheoremProverRunner {

    private AproveRunner aproveRunner = new AproveRunner();
    private ACL2Runner acl2Runner = new ACL2Runner();

    @Override
    public Pair<Boolean, Exportable> runTheoremProverOnInput(Formula frml, Program prgrm, String strategy, String timeLimit, Abortion aborter, RuntimeInformation rti) throws AbortionException, TheoremProverFailedException {
        long time;
        System.err.print("AProVE: ");
        time = System.currentTimeMillis();
        Pair<Boolean,Exportable> aproveResult = this.aproveRunner.runTheoremProverOnInput(frml, prgrm, strategy, timeLimit, aborter, rti);
        boolean aprove = aproveResult.x;
        System.err.println(aprove+" ("+(System.currentTimeMillis()-time)+"ms)");
        //if (!aprove) return false;
        System.err.print("ACL2: ");
        time = System.currentTimeMillis();
        Pair<Boolean, Exportable> acl2Result = this.acl2Runner.runTheoremProverOnInput(frml, prgrm, strategy, timeLimit, aborter, rti);
        boolean acl2 = acl2Result.x;
        System.err.println(acl2+" ("+(System.currentTimeMillis()-time)+"ms)");
        if (acl2) {
            System.err.println(this.acl2Runner.getACL(frml, prgrm, timeLimit));
        }
        if (aprove != acl2) {
            System.err.println(this.acl2Runner.getACL(frml, prgrm, timeLimit));
            try {
                final String DUMP_FILE = "/Users/nowonder/papers/induction/examples/qsort.acl";
                FileWriter writer = new FileWriter(new File(DUMP_FILE));
                writer.write(this.acl2Runner.getACL(frml, prgrm, timeLimit));
                writer.close();
                System.err.println("dumped to "+DUMP_FILE);
            } catch (IOException e) {
                e.printStackTrace();
            }
            throw new TheoremProverFailedException();
        }
        if (acl2) {
            return new Pair<Boolean,Exportable>(true,acl2Result.y);
        } else if (aprove) {
            return new Pair<Boolean,Exportable>(true,aproveResult.y);
        } else {
            return new Pair<Boolean,Exportable>(false,null);
        }
    }
}
