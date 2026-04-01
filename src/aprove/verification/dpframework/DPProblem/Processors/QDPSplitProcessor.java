package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Obligations.Junctors.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * Split Processor
 *
 * @author thiemann
 */

public class QDPSplitProcessor extends Processor.ProcessorSkeleton {

    private final BasicObligationNode relativeProof;
    private final List<BasicObligationNode> openObls;
    private final QDPProblem res;
    private final Set<Rule> Premoved, Rremoved;
    private boolean closed;

    public QDPSplitProcessor(
        final BasicObligationNode relativeProof,
        final List<BasicObligationNode> openObls,
        final QDPProblem res)
    {
        this.closed = false;
        this.relativeProof = relativeProof;
        this.res = res;
        this.openObls = openObls;
        final QDPProblem orig = (QDPProblem) relativeProof.getBasicObligation();
        final Set<Rule> P = new HashSet<Rule>(orig.getP());
        final Set<Rule> R = new HashSet<Rule>(orig.getR());
        final Set<Rule> remP = res.getP();
        final Set<Rule> remR = res.getR();
        if (Globals.useAssertions) {
            assert (R.containsAll(remR));
            assert (P.containsAll(remP));
        }
        P.removeAll(remP);
        R.removeAll(remR);
        this.Premoved = P;
        this.Rremoved = R;
    }

    @Override
    public boolean isApplicable(final BasicObligation o) {
        return true;
    }

    @Override
    public Result process(
        final BasicObligation bobl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        this.closeProof();
        final Proof proof =
            new SplitQDPProof(
                (QDPProblem) bobl,
                (QDPProblem) this.relativeProof.getBasicObligation(),
                this.res,
                this.Premoved,
                this.Rremoved);
        final Result res = ResultFactory.provedAnd(this.relativeProof, this.res, YNMImplication.EQUIVALENT, proof);
        return res;
    }

    private synchronized void closeProof() {
        if (this.closed) {
            return;
        }
        final ObligationNode nothing = JunctorObligationNode.create(Junctors.AND, new ArrayList<ObligationNode>(0));
        final ObligationNodeChild PisEmpty =
            new ObligationNodeChild(nothing, QDPProblemProcessor.pIsEmptyProof, YNMImplication.SOUND);
        for (final BasicObligationNode open : this.openObls) {
            open.addTechnique(PisEmpty, false);
        }
        this.closed = true;
    }

    public static class SplitQDPProof extends QDPProof {
        private final Set<Rule> Premoved;
        private final Set<Rule> Rremoved;
        private final QDPProblem origObl, relativeObl, newObl;

        private SplitQDPProof(
            final QDPProblem origObl,
            final QDPProblem relativeObl,
            final QDPProblem newObl,
            final Set<Rule> Premoved,
            final Set<Rule> Rremoved)
        {
            this.Premoved = Premoved;
            this.Rremoved = Rremoved;
            this.origObl = origObl;
            this.relativeObl = relativeObl;
            this.newObl = newObl;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s
                .append("We show in the first subproof that some pairs and rules can be removed, afterwards, we continue with the remaining DP-Problem");
            s.append(eu.cond_linebreak());
            if (!this.Premoved.isEmpty()) {
                this.result.append("We removed the following pairs:\n");
                this.result.append(eu.set(this.Premoved, Export_Util.RULES));
            }
            this.result.append(eu.cond_linebreak());
            if (!this.Rremoved.isEmpty()) {
                this.result.append("We removed the following rules:\n");
                this.result.append(eu.set(this.Rremoved, Export_Util.RULES));
            }
            return s.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            if (modus.isPositive()) {
                return CPFTag.DP_PROOF.create(doc,
                        CPFTag.SPLIT_PROC.create(
                                doc,
                                CPFTag.dps(doc, xmlMetaData, this.Premoved),
                                CPFTag.trs(doc, xmlMetaData, this.Rremoved),
                                childrenProofs[0],
                                childrenProofs[1]));
            } else {
                final int i = modus.negativeReason();
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, i == 0
                        ? this.relativeObl
                                : this.newObl);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

        @Override
        public boolean requireFullSubproof(final CPFModus modus, final int i) {
            return modus.isPositive() && i == 0;
        }

    }

}
