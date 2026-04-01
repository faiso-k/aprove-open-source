package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Narrowing.*;
import aprove.verification.oldframework.Haskell.Transformations.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Build the Termination Graph. Output are DP problems to show Termination and DP problems to show Non-Termination.
 * @author Stephan Swiderski
 */
@AcceptsStrategies(value = {"termiStrat", "nonTermiStrat" }, optional = true)
public class NarrowingProcessor extends HaskellGraphProcessor {

    private final boolean addTypes;

    private final UserStrategy nonTermiStrat;

    /**
     * @deprecated we do not have JDotty anymore
     */
    @Deprecated
    private final boolean show;

    private final UserStrategy termiStrat;

    /**
     * @param arguments The strategy arguments.
     */
    @ParamsViaArgumentObject
    public NarrowingProcessor(Arguments arguments) {
        super(
            arguments.nodeLimit,
            HaskellGraphProcessor.initGenParams(arguments.monoNestingDepth, arguments.multiNestingDepth)
        );
        this.show = arguments.show;
        this.addTypes = arguments.addTypes;
        this.termiStrat = arguments.termiStrat;
        this.nonTermiStrat = arguments.nonTermiStrat;
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
        final NarrowingGraphToDPs ngToDPs = new NarrowingGraphToDPs(prog.getModules(), narrowing.getFreeAppNode());
        List<HaskellPR> hPRs = ngToDPs.dpAnalyse(root);
        final Set<QDPProblem> QDPsTermination = new HashSet<QDPProblem>();
        for (HaskellPR hPR : hPRs) {
            QDPsTermination.add(
                HaskellToQTRSProblem.buildQDPProblemForTermination(prog.getModules(), hPR, this.addTypes, aborter)
            );
        }
        // The NarrowingProof that is shared
        final NarrowingProof np =
            new NarrowingProof(prog, null, ngToDPs.getGraph(), root.getChildren().get(0).getNum());
        // if there are no DP problems, there is nothing left to be shown
        if (QDPsTermination.isEmpty()) {
            return ResultFactory.proved(np);
        }
        final NarrowingGraphToNonTermDPs ngToNTDPs =
            new NarrowingGraphToNonTermDPs(prog.getModules(), narrowing.getFreeAppNode());
        hPRs = ngToNTDPs.dpAnalyse(root);
        final Set<QDPProblem> QDPsNonTermination = new HashSet<QDPProblem>();
        for (HaskellPR hPR : hPRs) {
            QDPsNonTermination.add(
                HaskellToQTRSProblem.buildQDPProblemForNonTermination(
                    prog.getModules(),
                    hPR,
                    this.addTypes,
                    aborter,
                    ngToNTDPs.getCcCheckEntity()
                )
            );
        }
        // Here, we are sure there is at least one DP problem both for Termination and for NonTermination
        final List<ExecutableStrategy> resultList = new ArrayList<ExecutableStrategy>(2);
        if (this.termiStrat != null) {
            final Result result = ResultFactory.provedAnd(QDPsTermination, YNMImplication.SOUND, np);
            // Apply termiStrat to result, wrapped in Solve()
            final ExecResult eResult = new ExecResult(rti, oblNode, result);
            final ExecSequence exStr = new ExecSequence(eResult, this.termiStrat, false, rti);
            final ExecutableStrategy exStrTermi = new ExecSolve(exStr, oblNode, rti);
            resultList.add(exStrTermi);
        }
        if (this.nonTermiStrat != null) {
            final Result result = ResultFactory.provedAnd(QDPsNonTermination, YNMImplication.COMPLETE, np);
            // Apply nonTermiStrat to result, wrapped in Solve()
            final ExecResult eResult = new ExecResult(rti, oblNode, result);
            final ExecSequence exStr = new ExecSequence(eResult, this.nonTermiStrat, false, rti);
            final ExecutableStrategy exStrNonTermi = new ExecSolve(exStr, oblNode, rti);
            resultList.add(exStrNonTermi);
        }
        return ResultFactory.justANewStrategy(ExecFirst.createFromExec(resultList, oblNode, rti));
    }

    public static class Arguments extends HaskellGraphProcessor.GraphProcessorArguments {

        public boolean addTypes = false;
        public UserStrategy nonTermiStrat = null;
        public boolean show = false;
        public UserStrategy termiStrat = null;

        public void setNonTerminationStrategy(String name) {
            this.nonTermiStrat = new VariableStrategy(name);
        }

        public void setTerminationStrategy(String name) {
            this.termiStrat = new VariableStrategy(name);
        }

    }

}
