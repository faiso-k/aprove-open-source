package aprove.verification.dpframework.HaskellProblem.Processors;

import java.io.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Bytecode.Processors.*;

public class HaskellDotDumpProcessor extends DumpProcessor {

    @ParamsViaArgumentObject
    public HaskellDotDumpProcessor(Arguments args) {
        super(args);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof HaskellProgram;
    }

    @Override
    public Result process(
        BasicObligation obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
    ) throws AbortionException {
        NarrowingToDOTProcessor.Arguments args = new NarrowingToDOTProcessor.Arguments();
        final File inputPath = new File((String)rti.getMetadata(Metadata.PROBLEM_PATH_NAME));
        final String problemName = inputPath.getName();
        final String fileName = problemName + "-" + obl.getId() + ".dot";
        args.fileName = this.getOutputDir() + File.separator + fileName;
        System.out.println("Dumping graph to " + args.fileName);
        return new NarrowingToDOTProcessor(args).process(obl, oblNode, aborter, rti);
    }

}
