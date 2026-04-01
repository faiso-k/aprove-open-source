package aprove.verification.oldframework.Bytecode.Processors;

import java.io.*;

import aprove.*;
import aprove.input.Programs.intClauses.*;
import aprove.input.Programs.pushdownSMT.*;
import aprove.input.Programs.t2.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.WeightedIntTrs.*;

/**
 * This processor takes a QDP or IntTRS obligation and dumps it into a file in the configured directory.
 */

public class TRSDumpProcessor extends DumpProcessor {

    @ParamsViaArgumentObject
    public TRSDumpProcessor(final Arguments args) {
        super(args);
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl instanceof QDPProblem || obl instanceof IRSwTProblem || obl instanceof T2IntSys || obl instanceof IntClausesSystem || obl instanceof SMTPushdownAutomaton || obl instanceof WeightedIntTrs || obl instanceof RuntimeComplexityTrsProblem);
    }

    @Override
    public Result process(final BasicObligation obl, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti)
    {
        try {
            final String outputDir = this.getOutputDir();

            if (obl instanceof IRSwTProblem) {
                final String path = dump((IRSwTProblem) obl, outputDir, rti, aborter);
                return ResultFactory.proved(obl, YNMImplication.EQUIVALENT, new DumpProof(path, "intTRS"));
            } else if (obl instanceof QDPProblem) {
                final String path = dump((QDPProblem) obl, outputDir, rti, aborter);
                return ResultFactory.proved(obl, YNMImplication.EQUIVALENT, new DumpProof(path, "QDP"));
            } else if (obl instanceof T2IntSys) {
                final String path = dump((T2IntSys) obl, outputDir, rti, aborter);
                return ResultFactory.proved(obl, YNMImplication.EQUIVALENT, new DumpProof(path, "T2Sys"));
            } else if (obl instanceof IntClausesSystem) {
                final String path = dump((IntClausesSystem) obl, outputDir, rti, aborter);
                return ResultFactory.proved(obl, YNMImplication.EQUIVALENT, new DumpProof(path, "IntClauses"));
            } else if (obl instanceof SMTPushdownAutomaton) {
                final String path = dump((SMTPushdownAutomaton) obl, outputDir, rti, aborter);
                return ResultFactory.proved(obl, YNMImplication.EQUIVALENT, new DumpProof(path, "SMTPushdown"));
            } else if (obl instanceof WeightedIntTrs) {
                final String path = dump((WeightedIntTrs) obl, outputDir, rti, aborter);
                return ResultFactory.proved(obl, BothBounds.create(), new DumpProof(path, "WeightedIntTrs"));
            } else if (obl instanceof RuntimeComplexityRelTrsProblem) {
                final String path = dump((RuntimeComplexityRelTrsProblem) obl, outputDir, rti, aborter);
                return ResultFactory.proved(obl, BothBounds.create(), new DumpProof(path, "CpxTrs"));
            }
            return ResultFactory.unsuccessful();
        } catch (DumpFailedException e) {
            return ResultFactory.error(e);
        }
    }

    private String dump(RuntimeComplexityRelTrsProblem obl, String outputDir, RuntimeInformation rti, Abortion aborter)
            throws DumpFailedException {
        final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        final String problemName = arguments.prefix + inputPath.getName();
        final String fileName = problemName + "-" + obl.getId() + ".trs";

        return DumpProcessor.dump(outputDir, fileName, obl.toExternString());
    }

    private String dump(final QDPProblem qdp,
        final String outputDir,
        final RuntimeInformation rti,
        final Abortion aborter) throws DumpFailedException {
        final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        final String problemName = arguments.prefix + inputPath.getName();
        final String fileName = problemName + "-" + qdp.getId() + ".qdp";

        return DumpProcessor.dump(outputDir, fileName, qdp.toExternString());
    }

    private String dump(final T2IntSys t2IntSys,
        final String outputDir,
        final RuntimeInformation rti,
        final Abortion aborter) throws DumpFailedException {
        final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        final String problemName = arguments.prefix + inputPath.getName();
        final String fileName = problemName + "-" + t2IntSys.getId() + ".t2";

        return DumpProcessor.dump(outputDir, fileName, t2IntSys.export(new PLAIN_Util()));
    }

    private String dump(final IntClausesSystem intClausesSystem,
                               final String outputDir,
                               final RuntimeInformation rti,
                               final Abortion aborter) throws DumpFailedException {
        final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        final String problemName = arguments.prefix + inputPath.getName();
        final String fileName = problemName + "-" + intClausesSystem.getId() + ".clauses.pl";

        return DumpProcessor.dump(outputDir, fileName, intClausesSystem.export(new PLAIN_Util()));
    }

    private String dump(final SMTPushdownAutomaton pushdownAut,
            final String outputDir,
            final RuntimeInformation rti,
            final Abortion aborter) throws DumpFailedException {
            final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
            final String problemName = arguments.prefix + inputPath.getName();
            final String fileName = problemName + "-" + pushdownAut.getId() + ".smt2";

            return DumpProcessor.dump(outputDir, fileName, pushdownAut.export(new PLAIN_Util()));
        }

    private String dump(final WeightedIntTrs intTrs,
            final String outputDir,
            final RuntimeInformation rti,
            final Abortion aborter) throws DumpFailedException {
            final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
            final String problemName = arguments.prefix + inputPath.getName() + (intTrs.getName() == null ? "" : "_" + intTrs.getName());
            final String fileName = problemName + "-" + intTrs.getId() + "_" + System.currentTimeMillis() + ".koat";

            if (Globals.DEBUG_THIES) {
                DumpProcessor.dump(outputDir, problemName + "-" + intTrs.getId() + ".dot", intTrs.toDOT());
            }

            return DumpProcessor.dump(outputDir, fileName, WeightedIntTrsToKoATProcessor.toKoAT(intTrs));
        }

    private String dump(final IRSwTProblem irswt,
        final String outputDir,
        final RuntimeInformation rti,
        final Abortion aborter) throws DumpFailedException
    {
        final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        final String problemName = arguments.prefix + inputPath.getName();
        final File path =
            new File(outputDir
                + System.getProperty("file.separator")
                + problemName
                + "-"
                + irswt.getId()
                + ".inttrs");

        FileWriter fw = null;
        try {
            fw = new FileWriter(path);
            if (irswt.getStartTerm() != null) {
                fw.write("Start: " + irswt.getStartTerm());
            }
            IRSwTProblem.exportRules(irswt.getRules(), aborter, fw);
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
        System.out.println("Dumped system to " + path.getPath());
        return path.getPath();
    }

}
