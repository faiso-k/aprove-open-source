/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Takes as input any DP problem (P,Q,R,a).
 * Sets the minimality flag by demanding that R is Q-terminating,
 * one can set a variable strategy S to prove Q-termination of R.
 * If this is done this strategy is successful only if by S one
 * can prove Q-termination of R and only the resulting problem
 * (P,Q,R,m) is returned.
 * If S is not specified then the and-Obligation of (R,Q) and
 * (P,Q,R,m) is returned.
 * @author thiemann
 */
public class IntroMinimalityProcessor extends QDPProblemProcessor {

    private final UserStrategy strategy;

    @ParamsViaArguments("Strategy")
    public IntroMinimalityProcessor(final String strategy) {
        this.strategy = this.parseStrategy(strategy);
    }

    public UserStrategy parseStrategy(final String name) {
        if (name == null) {
            return null;
        } else {
            final UserStrategy userStrat = new VariableStrategy(name);
            return new Solve(userStrat);
        }
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return !qdp.getMinimal();
    }

    @Override
    public Result processQDPProblem(final QDPProblem qdpProblem, final Abortion abortion) throws AbortionException{
        throw new RuntimeException("This method in IntroMinimalityProc should not be called!");
    }

    @Override
    public Result process(final BasicObligation o, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final QDPProblem qdp = (QDPProblem) o;

        assert(!qdp.getMinimal());
        final QDPProblem newQdp = qdp.getSameProblem(true);
        final QTRSProblem qtrs = newQdp.getRwithQ();
        if (this.strategy == null) {
            final List<BasicObligation> obls = new ArrayList<>(2);
            obls.add(qtrs);
            obls.add(newQdp);
            return ResultFactory
                .provedAnd(obls, YNMImplication.EQUIVALENT, new IntroMinimalityProof(qdp, newQdp, qtrs));
        } else {
            final BasicObligationNode newQDPObl =
 new BasicObligationNode(newQdp);
            final BasicObligationNode newQTRSObl =
                new BasicObligationNode(qtrs);
            final List<ObligationNode> obls = new ArrayList<ObligationNode>(2);
            obls.add(newQTRSObl);
            obls.add(newQDPObl);
            final ObligationNode andNode   = JunctorObligationNode.createAnd(obls);

            final ExecutableStrategy execStrat = this.strategy.getExecutableStrategy(newQTRSObl, rti);
            final ExecutableStrategy succStrat = new Success(newQDPObl);
            final List<ExecutableStrategy> vecStrat = new ArrayList<ExecutableStrategy>(2);
            vecStrat.add(execStrat);
            vecStrat.add(succStrat);

            final ExecutableStrategy allStrat  = new ExecAllSequential(vecStrat, rti);

            return ResultFactory.provedWithNewStrategy(
                andNode,
                YNMImplication.EQUIVALENT,
 new IntroMinimalityProof(
                qdp,
                newQdp,
                qtrs),
                allStrat);
        }
    }


    private static class IntroMinimalityProof extends QDPProof {

        QDPProblem origQDP, newQDP;
        QTRSProblem newQTRS;

        public IntroMinimalityProof(final QDPProblem origQDP, final QDPProblem newQDP, final QTRSProblem newQTRS) {
            this.origQDP = origQDP;
            this.newQDP = newQDP;
            this.newQTRS = newQTRS;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final String res = "To show that there are no infinite (P,Q,R)-chains it suffices to show that "+
                "there are no minimal infinite (P,Q,R)-chains and that R is Q-terminating.\n" +
                "Moreover, infiniteness of (P,Q,R,m) or Q-non termination of R implies infiniteness of (P,Q,R,a) " + o.cite(Citation.THIEMANN)+".";
            return o.export(res);
        }

    }


}
