package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Haskell.Narrowing.*;

/**
 * Abstract class for Haskell graph construction.
 * @author cryingshadow
 * @version $Id$
 */
public abstract class HaskellGraphProcessor extends Processor.ProcessorSkeleton {

    /**
     * The logger.
     */
    protected final static Logger logger = Logger.getLogger("aprove.verification.theoremprover.Haskell");

    /**
     * @param prog The Haskell program.
     * @param narrowing The Haskell narrowing.
     * @param aborter The aborter.
     * @return The root node of the computed Haskell graph. Null if this computation was not successful.
     * @throws AbortionException If it is aborted.
     */
    public static NarrowNode computeGraph(
        HaskellProgram prog,
        HaskellNarrowing narrowing,
        Abortion aborter
    ) throws AbortionException {
        return narrowing.develop(prog.getModules().getStartTerms(), aborter);
    }

    /**
     * @param mono TODO
     * @param multi TODO
     * @return TODO
     */
    public static GenParameters initGenParams(int mono, int multi) {
        GenParameters res = new GenParameters();
        res.monoNestingDepth = mono;
        res.multiNestingDepth = multi;
        return res;
    }

    /**
     * TODO
     */
    protected final GenParameters genParameters;

    /**
     * The node limit.
     */
    protected final int nodeLimit;

    /**
     * @param limit The node limit.
     * @param params TODO
     */
    public HaskellGraphProcessor(int limit, GenParameters params) {
        this.nodeLimit = limit;
        this.genParameters = params;
    }

    @Override
    public Result process(
        BasicObligation obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
    ) throws AbortionException {
        final HaskellProgram prog = ((HaskellProgram)obl).deepcopy();
        final HaskellNarrowing narrowing = new HaskellNarrowing(prog.getModules(), this.nodeLimit, this.genParameters);
        NarrowNode root;
        try {
            root = HaskellGraphProcessor.computeGraph(prog, narrowing, aborter);
        } catch (AbortionException e) {
            if (aprove.Globals.aproveVersion == aprove.Globals.AproveVersion.DEVELOPER_VERSION) {
                HaskellGraphProcessor.logger.log(Level.FINEST, "Haskell Narrowing was aborted!");
            }
            return ResultFactory.aborted(e);
        }
        if (root == null) {
            return ResultFactory.unsuccessful();
        }
        return this.processGraph(oblNode, prog, narrowing, root, aborter, rti);
    }

    /**
     * @param oblNode The obligation node.
     * @param prog The Haskell program.
     * @param narrowing The Haskell narrowing.
     * @param root The root of the Haskell graph.
     * @param aborter For abortions.
     * @param rti Runtime information.
     * @return The result of the processor.
     * @throws AbortionException If this processor is aborted.
     */
    protected abstract Result processGraph(
        BasicObligationNode oblNode,
        HaskellProgram prog,
        HaskellNarrowing narrowing,
        NarrowNode root,
        Abortion aborter,
        RuntimeInformation rti
    ) throws AbortionException;

    /**
     * Super class for graph processor arguments.
     * @author cryingshadow
     * @version $Id$
     */
    protected static abstract class GraphProcessorArguments {

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
