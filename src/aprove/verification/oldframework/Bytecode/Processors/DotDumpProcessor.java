package aprove.verification.oldframework.Bytecode.Processors;

import java.io.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;

/**
 * This processor takes dot-able (e.g. JBCTerminationGraph) obligation and dumps it into a dot-file in the configured directory.
 */

public class DotDumpProcessor extends DumpProcessor {

    @ParamsViaArgumentObject
    public DotDumpProcessor(final Arguments args) {
        super(args);
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl instanceof DOT_Able || obl instanceof DOTmodern_Able);
    }

    @Override
    public Result process(final BasicObligation obl, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti)
    {
        final String outputDir = this.getOutputDir();
        try {
            final String path = DotDumpProcessor.dump(obl, outputDir, rti, aborter);
            return ResultFactory.proved(new DumpProof(path, "graph"));
        } catch (DumpFailedException e) {
            return ResultFactory.error(e);
        }
    }

    private static String dump(final BasicObligation graph,
        final String outputDir,
        final RuntimeInformation rti,
        final Abortion aborter) throws DumpFailedException {
        final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        final String problemName = inputPath.getName();
        final String fileName = problemName + "-" + graph.getId() + ".dot";

        if (graph instanceof DOT_Able) {
            return DumpProcessor.dump(outputDir, fileName, ((DOT_Able)graph).toDOT());
        } else {
            assert graph instanceof DOTmodern_Able : "The DotDumpProcessor is only applicable for dot-able obligations!";
            return DumpProcessor.dump(outputDir, fileName, ((DOTmodern_Able)graph).toDOT());
        }
    }

}
