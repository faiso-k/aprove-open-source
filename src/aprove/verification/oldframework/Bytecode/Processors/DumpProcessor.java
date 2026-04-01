package aprove.verification.oldframework.Bytecode.Processors;

import java.io.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;

public abstract class DumpProcessor extends Processor.ProcessorSkeleton {

    /** Where we are gonna dump this. */
    public static String outputDir = null;

    /**
     * Convenience class holding arguments passed in from the strategy.
     */
    public static class Arguments {
        /** Where we are gonna dump this. */
        public String outputDir = null;
        public String prefix = "";
    }

    /**
     * Parameters for this processor.
     */
    final Arguments arguments;

    @ParamsViaArgumentObject
    protected DumpProcessor(final Arguments args) {
        this.arguments = args;
    }

    protected String getOutputDir() {
        if (DumpProcessor.outputDir == null && this.arguments.outputDir == null) {
            throw new RuntimeException("Don't know where to dump (not specified)!");
        } else if (DumpProcessor.outputDir != null && this.arguments.outputDir != null
            && !DumpProcessor.outputDir.equals(this.arguments.outputDir)) {
            throw new RuntimeException(
                "Don't know where to dump (static field and processor argument contradict each other)!");
        }

        if (DumpProcessor.outputDir != null) {
            return DumpProcessor.outputDir;
        } else {
            return this.arguments.outputDir;
        }
    }

    public static String dump(final String outputDir, final String fileName, final String output) throws DumpFailedException {
        final File path = new File(outputDir + System.getProperty("file.separator") + fileName);

        FileWriter fw = null;
        try {
            fw = new FileWriter(path);
            fw.append(output);
        } catch (final IOException e) {
            System.err.println("Could not write output, aborting: " + e.getMessage());
            throw new DumpFailedException();
        } finally {
            if (fw != null) {
                try {
                    fw.close();
                } catch (final IOException e) {
                    System.err.println("Could not write output, aborting: " + e.getMessage());
                    throw new DumpFailedException();
                }
            }
        }
        System.out.println("Dumped to " + path.getPath());
        return path.getPath();
    }

    /**
     * A very fine proof.
     * @author marc (don't blame me)
     */
    public class DumpProof extends DefaultProof {
        /** Path of the generated output file. */
        final String outputPath;

        /** Name of the obligation type (ie "intTRS" or "QDP"). */
        final String oblType;

        /**
         * Create the proof.
         * @param oP Path of the generated output file.
         * @param t
         */
        public DumpProof(final String oP, final String oblT) {
            super();
            this.outputPath = oP;
            this.oblType = oblT;
            this.shortName = oblT + "Dump";
            this.longName = oblT + " Dump";
        }

        /**
         * @param o export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Dumped " + this.oblType + " into " + this.outputPath + ".\n\n";
        }
    }
}
