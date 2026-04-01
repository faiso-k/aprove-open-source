package aprove.verification.dpframework.HaskellProblem.Processors;

import java.io.*;

import org.json.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Bytecode.Processors.*;
import aprove.verification.oldframework.Haskell.Narrowing.*;

/**
 * Dumps Haskell graphs to JSON.
 * @author jhensel, cryingshadow
 * @version $Id$
 */
public class HaskellJSONDumpProcessor extends DumpProcessor {

    /**
     * TODO
     */
    private final int monoNestingDepth;

    /**
     * TODO
     */
    private final int multiNestingDepth;

    /**
     * The node limit.
     */
    private final int nodeLimit;

    /**
     * @param args Strategy arguments.
     */
    @ParamsViaArgumentObject
    public HaskellJSONDumpProcessor(Arguments args) {
        super(args);
        this.nodeLimit = args.nodeLimit;
        this.monoNestingDepth = args.monoNestingDepth;
        this.multiNestingDepth = args.multiNestingDepth;
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
        final HaskellProgram prog = (HaskellProgram)obl;
        try {
            NarrowNode root =
                HaskellGraphProcessor.computeGraph(
                    prog,
                    new HaskellNarrowing(
                        prog.getModules(),
                        this.nodeLimit,
                        HaskellGraphProcessor.initGenParams(this.monoNestingDepth, this.multiNestingDepth)
                    ),
                    aborter
                );
            if (root == null) {
                return ResultFactory.unsuccessful();
            }
            return
                ResultFactory.proved(
                    new DumpProof(
                        DumpProcessor.dump(
                            DumpProcessor.outputDir,
                            new File((String)rti.getMetadata(Metadata.PROBLEM_PATH_NAME)).getName()
                            + "-"
                            + obl.getId()
                            + ".json",
                            root.toJSONObject(prog.getModules().getMainModule()).toString(2)
                        ),
                        "graph"
                    )
                );
        } catch (JSONException | DumpFailedException e) {
            return ResultFactory.error(e);
        }
    }

    /**
     * Strategy arguments.
     * @author cryingshadow
     * @version $Id$
     */
    public static class Arguments extends DumpProcessor.Arguments {

        /**
         * TODO
         */
        public int monoNestingDepth = 6;

        /**
         * TODO
         */
        public int multiNestingDepth = 3;

        /**
         * The node limit.
         */
        public int nodeLimit = 50000;

    }

}
