/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import aprove.xml.*;

/**
 * Processor according to Thm. 3.34 and Thm 3.38 in the thesis.
 * If KeepMinimality is true (default), then the processor
 * checks whether some term f(..) in Q occur where f does not occur in P cup R. Then
 * this term f(..) can be safely deleted from Q if one is in the innermost case.
 *
 * If KeepMinimality is false, then the processor does not require  innermost case
 * and it can delete all terms in Q which contain a symbol that is not present in
 * P cup R. However, then minimality cannot be carried over.
 *
 * @author thiemann
 */
public class QDPQReductionProcessor extends QDPProblemProcessor {

    private final boolean keepMinimality;

    @ParamsViaArgumentObject
    public QDPQReductionProcessor(final Arguments arguments) {
        this.keepMinimality = arguments.keepMinimality;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        if (! (Options.certifier.isNone() || Options.certifier.isCeta())) {
            return false;
        }
        final QTermSet Q = qdp.getQ();
        if (Q.isEmpty()) {
            return false;
        }
        if (this.keepMinimality && qdp.getMinimal() && !qdp.QsupersetOfLhsR()) {
            return false;
        }

        final Set<FunctionSymbol> PRsig = qdp.getPRSignature();
        if (this.keepMinimality && qdp.getMinimal()) {
            for (final TRSFunctionApplication q : Q.getTerms()) {
                if (!PRsig.contains(q.getRootSymbol())) {
                    return true;
                }
            }
        } else {
            for (final TRSFunctionApplication q : Q.getTerms()) {
                if (!PRsig.containsAll(q.getFunctionSymbols())) {
                    return true;
                }
            }
        }
        return false;
    }


    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        final Set<FunctionSymbol> PRsig = qdp.getPRSignature();

        QTermSet Q = qdp.getQ();
        final Set<TRSFunctionApplication> origQ = Q.getTerms();
        final Set<TRSFunctionApplication> newQ = new LinkedHashSet<TRSFunctionApplication>(origQ.size());
        final Set<TRSFunctionApplication> deletedQ =  new LinkedHashSet<TRSFunctionApplication>(5);

        boolean preserveMinimality = qdp.QsupersetOfLhsR(); // can minimality be preserved
        final boolean keepMinimality = this.keepMinimality && qdp.getMinimal(); // do we have to care about minimality?
        for (final TRSFunctionApplication fTerm : origQ) {
            if (!PRsig.contains(fTerm.getRootSymbol())) {
                deletedQ.add(fTerm);
            } else {
                if (!keepMinimality && !PRsig.containsAll(fTerm.getFunctionSymbols())) {
                    deletedQ.add(fTerm);
                    preserveMinimality = false;
                } else {
                    newQ.add(fTerm);
                }
            }
        }

        Q = new QTermSet(newQ);

        final QDPProblem newQdp = qdp.getSubProblemWithSmallerQ(Q, qdp.getMinimal() && preserveMinimality);

        final Proof proof = new QReductionProof(deletedQ, qdp, newQdp, preserveMinimality);

        return ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);
    }

    private static class QReductionProof extends Proof {

        private final Set<TRSFunctionApplication> deletedFromQ;
        private final QDPProblem origQdp;
        private final QDPProblem newQdp;
        private final boolean preserveMinimality;

        private QReductionProof(final Set<TRSFunctionApplication> deletedFromQ, final QDPProblem origQdp, final QDPProblem newQdp, final boolean preserveMinimality) {
            this.deletedFromQ = deletedFromQ;
            this.origQdp = origQdp;
            this.newQdp = newQdp;
            this.preserveMinimality = preserveMinimality;
        }

        @Override
        public String export(final Export_Util o) {
            final StringBuilder s = new StringBuilder();
            if (this.preserveMinimality) {
                s.append(o.export("We deleted the following terms from Q as each root-symbol of these terms does neither occur in P nor in R."));
            } else {
                s.append(o.export("We deleted the following terms from Q as they contain symbols which do neither occur in P nor in R."));
            }
            s.append(o.cite(Citation.THIEMANN) + ".");
            s.append(o.cond_linebreak());
            s.append(o.set(this.deletedFromQ, Export_Util.RULES));
            s.append(o.cond_linebreak());
            return s.toString();
        }

        @Override
        public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
            final Element e = XMLTag.QDP_QREDUCTION.createElement(doc);
            e.appendChild(this.newQdp.getQ().toDOM(doc, xmlMetaData));
            return e;
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            final Element e = CPFTag.INNERMOST_LHSS_REMOVAL_PROC.createElement(doc);
            e.appendChild(this.newQdp.getQ().toCPF(doc, xmlMetaData));
            e.appendChild(childrenProofs[0]);
            return (modus.isPositive() ? CPFTag.DP_PROOF : CPFTag.DP_NONTERMINATION_PROOF).create(doc, e);
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }

    public static class Arguments {
        public boolean keepMinimality = true;
    }

}
