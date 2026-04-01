package aprove.verification.oldframework.IntTRS;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Take a KITTeL problem and ask KITTeL about it.
 *
 * @author Marc Brockschmidt
 */
public class KITTeLProcessor extends Processor.ProcessorSkeleton {
    /** The log facility used for debugging stuff. */
    private static final Logger LOG = Logger.getLogger("aprove.verification.oldframework.Bytecode.Processors.ToKITTel.KITTeLProcessor");

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSProblem p;
        if (obl instanceof IRSProblem) {
            p = (IRSProblem) obl;
        } else {
            // Try to convert
            p = new IRSProblem((IRSwTProblem) obl);
        }

        final Process process;
        File input = null;
        Scanner sc = null;
        Scanner errors = null;
        final List<String> kittelProof = new LinkedList<String>();
        boolean proved = false;
        try {
            //Write our data:
            aborter.checkAbortion();
            input = File.createTempFile("APRoVEExternal", ".kittel");
            input.deleteOnExit();
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            IRSwTProblem.exportRules(p.getRules(), aborter, inputWriter);
            inputWriter.close();
            KITTeLProcessor.LOG.log(Level.FINER, "Wrote KITTeL input.");
            aborter.checkAbortion();

            //Call KITTeL
            final ArrayList<String> parameters = new ArrayList<String>();
            parameters.add("kittel");
            parameters.add("--timeout");
            parameters.add("5");
            parameters.add(input.getCanonicalPath());
            final ProcessBuilder processBuilder = new ProcessBuilder(parameters.toArray(new String[parameters.size()]));
            process = processBuilder.start();
            TrackerFactory.process(aborter, process);
            try {
                process.waitFor();
            } catch (final InterruptedException e) {
                assert false : "KITTeL interrupted!";
            }

            //Parse output
            errors = new Scanner(new BufferedInputStream(process.getErrorStream()));
            while (errors.hasNextLine()) {
                System.err.println("KITTeL stderr: " + errors.nextLine());
            }
            errors.close();

            sc = new Scanner(new BufferedInputStream(process.getInputStream()));
            while (sc.hasNextLine()) {
                final String line = sc.nextLine();
                if (line.contains("Termination successfully shown")) {
                    proved = true;
                }
                kittelProof.add(line);
            }
        } catch (final IOException e) {
            e.printStackTrace();
        } finally {
            if (sc != null) {
                sc.close();
            }
            if (errors != null) {
                errors.close();
            }
        }

        if (proved) {
            return ResultFactory.proved(new KITTeLProof(kittelProof));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
    }

    private static class KITTeLProof extends Proof.DefaultProof {
        private final List<String> proofStrs;

        public KITTeLProof(final List<String> proof) {
            this.setShortName("KITTeLProof");
            this.setLongName("KITTeLProof");
            this.proofStrs = proof;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder();
            for (final String s : this.proofStrs) {
                result.append(s);
                result.append(o.newline());
            }
            return result.toString();
        }
    }
}
