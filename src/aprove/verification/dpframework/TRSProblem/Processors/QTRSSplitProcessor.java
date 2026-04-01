package aprove.verification.dpframework.TRSProblem.Processors;


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
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * Split Processor
 *
 * @author thiemann
 */

public class QTRSSplitProcessor extends Processor.ProcessorSkeleton  {

    private final BasicObligationNode relativeProof;
    private final List<BasicObligationNode> openObls;
    private final QTRSProblem res;
    private final Set<Rule> Rremoved;
    private boolean closed;

    public QTRSSplitProcessor(final BasicObligationNode relativeProof, final List<BasicObligationNode> openObls, final QTRSProblem res) {
        this.closed = false;
        this.relativeProof = relativeProof;
        this.res = res;
        this.openObls = openObls;
        final QTRSProblem orig = (QTRSProblem) relativeProof.getBasicObligation();
        final Set<Rule> R = new HashSet<Rule>(orig.getR());
        final Set<Rule> remR = res.getR();
        if (Globals.useAssertions) {
            assert (R.containsAll(remR));
        }
        R.removeAll(remR);
        this.Rremoved = R;
    }

    @Override
    public boolean isApplicable(final BasicObligation o) {
        return true;
    }

    @Override
    public Result process(final BasicObligation bobl, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        this.closeProof();
        final Proof proof =
            new SplitQTRSProof(
                (QTRSProblem) bobl,
                (QTRSProblem) this.relativeProof.getBasicObligation(),
                this.res,
                this.Rremoved);
        final Result res = ResultFactory.provedAnd(this.relativeProof, this.res, YNMImplication.EQUIVALENT, proof);
        return res;
    }

    private synchronized void closeProof() {
        if (this.closed) {
            return;
        }
        final ObligationNode nothing = JunctorObligationNode.create(Junctors.AND, new ArrayList<ObligationNode>(0));
        final ObligationNodeChild PisEmpty = new ObligationNodeChild(nothing, QTRSProcessor.rIsEmptyProof, YNMImplication.SOUND);
        for (final BasicObligationNode open : this.openObls) {
            open.addTechnique(PisEmpty, false);
        }
        this.closed = true;
    }

    private class SplitQTRSProof extends QTRSProof {
        private final Set<Rule> Rremoved;
        private final QTRSProblem origObl, relativeObl, newObl;

        private SplitQTRSProof(
            final QTRSProblem origObl,
            final QTRSProblem relativeObl,
            final QTRSProblem newObl,
                final Set<Rule> Rremoved) {
            this.Rremoved = Rremoved;
            this.origObl = origObl;
            this.relativeObl = relativeObl;
            this.newObl = newObl;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level){
            final StringBuilder s = new StringBuilder();
            s.append("We show in the first subproof that some rules can be removed, afterwards, we continue with the remaining TRS");
            s.append(eu.cond_linebreak());
            if (! this.Rremoved.isEmpty()) {
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
                return CPFTag.TRS_TERMINATION_PROOF.create(doc, CPFTag.SPLIT.create(
                    doc,
                    CPFTag.trs(doc, xmlMetaData, this.Rremoved),
                    childrenProofs[0],
                    childrenProofs[1]));
            } else {
                final int i = modus.negativeReason();
                return super.ruleRemovalNontermProof(doc, childrenProofs[i], xmlMetaData, i == 0
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
