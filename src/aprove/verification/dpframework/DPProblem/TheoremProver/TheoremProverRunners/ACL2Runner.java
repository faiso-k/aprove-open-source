package aprove.verification.dpframework.DPProblem.TheoremProver.TheoremProverRunners;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class ACL2Runner implements TheoremProverRunner {

    public static final String COMMAND = "acl2";
    public static final boolean FULL_LISTS = true;

    protected static final Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.TheoremProver.TheoremProverRunners.ACL2Runner");

    public String getACL(Formula frml, Program prgrm, String timeLimit) {
        StringBuffer sb = new StringBuffer();
        int indent = 0;
        boolean fullLists = ACL2Runner.FULL_LISTS;
        FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.ACL2);
        sb.append("(set-ruler-extenders :all)\n");
        prgrm.toACL2(sb,indent,fng,fullLists);
        sb.append("\n");
        if (timeLimit != null) {
            sb.append("(with-prover-time-limit "+timeLimit+"\n  ");
            indent++;
        }
        frml.toACL2(sb,indent,fng,fullLists,prgrm.hasBinarySort());
        if (timeLimit != null) {
            indent--;
            sb.append("\n)");
        }
        return sb.toString();
    }

    @Override
    public Pair<Boolean, Exportable> runTheoremProverOnInput(Formula frml, Program prgrm, String strategy, String timeLimit, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        final String acl = this.getACL(frml, prgrm, timeLimit);
        Process process = null;
        Scanner sc = null;
        try {
            ACL2Runner.log.log(Level.FINER, "Invoking {0}\n", ACL2Runner.COMMAND);
            long time = System.currentTimeMillis();
            aborter.checkAbortion();
            process = Runtime.getRuntime().exec(ACL2Runner.COMMAND);
            TrackerFactory.process(aborter, process);
            aborter.checkAbortion();
            Writer writer = new OutputStreamWriter(new BufferedOutputStream(process.getOutputStream(),acl.length()+4096));
            writer.write(acl);
            writer.flush();
            writer.close();
            aborter.checkAbortion();
            sc = new Scanner(process.getInputStream());
            boolean successful = false;
            StringBuilder sb = new StringBuilder();
            while (sc.hasNextLine()) {
                String line = sc.nextLine();
                sb.append(line);
                sb.append("\n");
                ACL2Runner.log.log(Level.FINEST, "{0}\n", line);
                if (line.startsWith(" TEST")) {
                    successful = true;
                }
                aborter.checkAbortion();
            }
            sc.close();
            final String acl2 = sb.toString();
            ACL2Runner.log.log(Level.FINER, "{0}: {1}\n",new Object[] {successful, System.currentTimeMillis()-time});
            return new Pair<Boolean, Exportable>(successful, new Exportable() {
                @Override
                public String export(Export_Util o) {
                    StringBuilder sb = new StringBuilder();
                    sb.append("The following input was given to ACL2:");
                    sb.append(o.linebreak());
                    sb.append(o.preFormatted(acl));
                    sb.append(o.linebreak());
                    sb.append(o.cond_linebreak());
                    sb.append("The following output was given by ACL2:");
                    sb.append(o.preFormatted(acl2));
                    return sb.toString();
                }
            });
        } catch (NoSuchElementException e) {
            // just return null
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            if (sc != null) {
                sc.close();
            }
            if (process != null) {
                process.destroy();
            }
        }
        return new Pair<Boolean,Exportable>(false,null);
    }

}
