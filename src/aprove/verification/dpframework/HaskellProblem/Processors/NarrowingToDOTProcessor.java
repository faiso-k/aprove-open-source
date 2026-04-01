package aprove.verification.dpframework.HaskellProblem.Processors;

import java.io.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Haskell.Narrowing.*;

/**
 * Build the Termination Graph and output it as DOT file.
 * @author cryingshadow
 */
public class NarrowingToDOTProcessor extends HaskellGraphProcessor {

    /**
     * The file name for the DOT output.
     */
    private String fileName;

    /**
     * @param arguments Strategy arguments.
     */
    @ParamsViaArgumentObject
    public NarrowingToDOTProcessor(Arguments arguments) {
        super(
            arguments.nodeLimit,
            HaskellGraphProcessor.initGenParams(arguments.monoNestingDepth, arguments.multiNestingDepth)
        );
        this.fileName = arguments.fileName;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof HaskellProgram);
    }

    @Override
    protected Result processGraph(
        BasicObligationNode oblNode,
        HaskellProgram prog,
        HaskellNarrowing narrowing,
        NarrowNode root,
        Abortion aborter,
        RuntimeInformation rti
    ) throws AbortionException {
        if (this.fileName == null) {
            return ResultFactory.error("No target file is specified!");
        }
        final NarrowingGraphToDOT ngToDOT = new NarrowingGraphToDOT(prog.getModules(), narrowing.getFreeAppNode());
        String res = ngToDOT.buildDOT(root);
        try (FileWriter writer = new FileWriter(new File(this.fileName))) {
            writer.write(res);
            writer.close();
        } catch (IOException e) {
            return ResultFactory.error(e);
        }
        return
            ResultFactory.proved(
                new NarrowingProof(prog, null, ngToDOT.getGraph(), root.getChildren().get(0).getNum())
            );
    }

    /**
     * Strategy arguments.
     * @author cryingshadow
     * @version $Id$
     */
    public static class Arguments extends HaskellGraphProcessor.GraphProcessorArguments {

        /**
         * The file name for the DOT output.
         */
        public String fileName = null;

        /**
         * @param name The file name for the DOT output.
         */
        public void setFileName(String name) {
            this.fileName = name;
        }

    }

}
