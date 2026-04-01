package aprove.verification.oldframework.Bytecode.Processors;

import java.io.*;

import org.json.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.JBCProblem.*;

/**
 * This processor takes json-able (e.g. Termination Graph) obligation and dumps it into a json-file in the configured directory.
 */

public class JSONDumpProcessor extends DumpProcessor {

    @ParamsViaArgumentObject
    public JSONDumpProcessor(final Arguments args) {
        super(args);
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof JBCTerminationGraphProblem;
    }

    @Override
    public Result process(final BasicObligation obl, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti)
    {
        final String outputDir = this.getOutputDir();

        try {
            final String path = JSONDumpProcessor.dump(obl, outputDir, rti, aborter);
            return ResultFactory.proved(new DumpProof(path, "graph"));
        } catch (JSONException | DumpFailedException e) {
            return ResultFactory.error(e);
        }
    }

    private static String dump(final BasicObligation graph,
        final String outputDir,
        final RuntimeInformation rti,
        final Abortion aborter) throws JSONException, DumpFailedException {
        final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        final String problemName = inputPath.getName();
        final String fileName = problemName + "-" + graph.getId() + ".json";

        final JBCTerminationGraphProblem termGraph = (JBCTerminationGraphProblem) graph;
        return DumpProcessor.dump(outputDir, fileName, termGraph.getGraph().toJSON().toString(2));
    }

}
