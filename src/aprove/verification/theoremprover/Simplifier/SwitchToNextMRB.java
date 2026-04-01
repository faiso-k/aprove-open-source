package aprove.verification.theoremprover.Simplifier;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Switches to the next Mutual Recursive Block (MRB) and marks previous MRB as terminating if that has been found out
 */
public class SwitchToNextMRB extends Processor.ProcessorSkeleton {

    private final UserStrategy strategy;
    private final boolean useKnownTermination;

    private final static Logger log = Logger.getLogger("aprove.verification.theoremprover.Simplifier.SwitchToNextMRB");

    @Deprecated
    public SwitchToNextMRB() {
        this(new Arguments());
        SwitchToNextMRB.log.warning("Use of deprecated constructor. Fix SimplifierSwitchToNextMRBItem!");
    }

    @ParamsViaArgumentObject
    public SwitchToNextMRB(final Arguments arguments) {
        super();
        this.strategy = this.parseDPsStrategy(arguments.DPsStrategy);
        this.useKnownTermination = arguments.UseKnownTermination;
    }

    public UserStrategy parseDPsStrategy(final String name) {
        if (name == null) {
            return null;
        }
        final UserStrategy userStrat = new VariableStrategy(name);
        return new Solve(userStrat);
    }

    @Override
    public Result process(final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {

        final SimplifierObligation sObl = ((SimplifierProblem) obl).getSimplifierObligation();

        final SimplifierObligation newSObl = sObl.shallowcopy();
        newSObl.switchToNextMRB();
        BasicObligation newSimplObl;

        // if there are no more MRBs to handle, return only the TRS
        if (newSObl.finished()) {
            newSimplObl = null;
        } else {
            newSimplObl = new SimplifierProblem(newSObl);
        }

        // in this case this was the first application, i.e. after a transformation into a SimplifierObligation
        // then only switch to the first MRB and return
        if (sObl.getCurrentDefs().isEmpty()) {
            return ResultFactory.proved(newSimplObl, YNMImplication.EQUIVALENT,
                new SwitchProof(true, null, null, false));
        }

        final SwitchProof p;
        final CurrentMutualRecursiveBlockToTRSProcessor cMRB2TRSProc =
            new CurrentMutualRecursiveBlockToTRSProcessor(this.useKnownTermination);
        final Result res = cMRB2TRSProc.process(obl, oblNode, aborter, rti);
        if (res.getStrategy().isFail()) {
            throw new RuntimeException("Could not convert SimplifierObligation to TRS!");
        }
        //        BasicObligation trsObl = res.getObligationChild().x.getBasicObligation();

        final Proof dpsProof = res.getObligationChild().getProof();

        final Set<DefFunctionSymbol> terminatingDefs = cMRB2TRSProc.getTerminatingDefs();

        // in case there is no strategy supplied the TRS will remain unhandled and only the simplification will continue
        if (this.strategy == null) {

            final List<BasicObligationNode> oblNodes = new Vector<BasicObligationNode>(2);

            oblNodes.add(res.getSuccessPosition());
            if (newSimplObl != null) {
                oblNodes.add(new BasicObligationNode(newSimplObl));
            }

            return ResultFactory.provedAndFromOblNodes(oblNodes, YNMImplication.EQUIVALENT, new SwitchProof(
                (newSimplObl != null), dpsProof, terminatingDefs, this.useKnownTermination));

        } else { // we have a strategy to apply to the TRS
            final BasicObligationNode trsNode = res.getSuccessPosition();

            final Implication resImplication = res.getObligationChild().getImplication();

            final Vector<ObligationNode> newOblNodes = new Vector<ObligationNode>(2);
            newOblNodes.add(trsNode);

            BasicObligationNode simplNode = null;
            // only add if there is a next MRB
            if (newSimplObl != null) {
                simplNode = new BasicObligationNode(newSimplObl);
                newOblNodes.add(simplNode);
            }

            final ObligationNode andNode = JunctorObligationNode.createAnd(newOblNodes);

            final ExecutableStrategy execTRSStrat = this.strategy.getExecutableStrategy(trsNode, rti);
            ExecutableStrategy succStrat = null;
            if (newSimplObl != null) {
                succStrat = new Success(simplNode);
            } else {
                succStrat = new Success(trsNode);
            }
            final Vector<ExecutableStrategy> execSuccStrats = new Vector<ExecutableStrategy>(2);
            execSuccStrats.add(execTRSStrat);
            execSuccStrats.add(succStrat);

            final ExecutableStrategy allSeqStrat = new ExecAllSequential(execSuccStrats, rti);

            return ResultFactory.provedWithNewStrategy(andNode, resImplication, new SwitchProof((newSimplObl != null),
                dpsProof, terminatingDefs, this.useKnownTermination), allSeqStrat);
        }

    }

    @Override
    public boolean isApplicable(final BasicObligation o) {
        return (o instanceof SimplifierProblem);
    }

    private static class SwitchProof extends Proof.DefaultProof {
        private final boolean hasNextMRB;
        private final Proof dpsProof;
        private final Set<DefFunctionSymbol> terminatingDefs;
        private final boolean useKnownTermination;

        private SwitchProof(final boolean hasNextMRB, final Proof dpsProof, final Set<DefFunctionSymbol> terminDefs,
                final boolean useKnownTermination) {
            this.shortName = "Switch MRBs";
            this.longName = "Switch to next MRB";
            this.hasNextMRB = hasNextMRB;
            this.dpsProof = dpsProof;
            this.terminatingDefs = terminDefs;
            this.useKnownTermination = useKnownTermination;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            String switchProofExported = "";
            if (this.hasNextMRB) {
                switchProofExported = "Switched to next Mutual Recursive Block." + o.newline();
            }

            String dpsProofExported = "";
            if (this.dpsProof != null) {
                dpsProofExported =
                    "The current MRB was transformed into a TRS " + o.italic("R")
                        + " whose Dependency Pairs remain to be proven." + o.newline();
                dpsProofExported += this.dpsProof.export(o);
            }

            String terminatingDefsExported = "";
            if ((this.dpsProof != null) && (!this.terminatingDefs.isEmpty())) {
                terminatingDefsExported +=
                    o.newline() + "Here, the following functions were considered to be terminating:" + o.newline();
                terminatingDefsExported += o.indent(o.exportToEnumeratingText(this.terminatingDefs, ",")) + o.newline();
            }

            return switchProofExported + dpsProofExported + terminatingDefsExported;
        }
    }

    public static class Arguments {
        public String DPsStrategy = null;
        public boolean UseKnownTermination = false;
    }

}
