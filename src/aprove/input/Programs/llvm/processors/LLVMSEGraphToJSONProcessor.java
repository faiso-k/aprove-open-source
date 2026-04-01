package aprove.input.Programs.llvm.processors;

import java.io.*;

import org.json.*;

import aprove.input.Programs.llvm.problems.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Bytecode.Processors.*;

/**
 * This processor takes json-able (e.g. SEGraph) obligation and dumps it into a json-file in the configured directory.
 */
public class LLVMSEGraphToJSONProcessor extends DumpProcessor {

    @ParamsViaArgumentObject
    public LLVMSEGraphToJSONProcessor(final Arguments args) {
        super(args);
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return (obl instanceof LLVMSEGraphProblem);
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti
    ) {
        try {
            final String path = LLVMSEGraphToJSONProcessor.dump(obl, DumpProcessor.outputDir, rti, aborter);
            return ResultFactory.proved(new DumpProof(path, "graph"));
        } catch (JSONException | DumpFailedException e) {
            return ResultFactory.error(e);
        }
    }

    private static String dump(
        final BasicObligation graph,
        final String dir,
        final RuntimeInformation rti,
        final Abortion aborter
    ) throws JSONException, DumpFailedException {
        final File inputPath = new File((String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        final String problemName = inputPath.getName();
        final String fileName = problemName + "-" + graph.getId() + ".json";

        final LLVMSEGraphProblem SEGraph = (LLVMSEGraphProblem) graph;
        return DumpProcessor.dump(dir, fileName, SEGraph.getGraph().toJSON().toString(2));
    }

}
