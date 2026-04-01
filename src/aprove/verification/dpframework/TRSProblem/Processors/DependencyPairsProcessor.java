package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Processor which creates out of a given QTRS a new QDPProblem where P contains all dependency pairs of R.
 *
 * @author Matthias Sondermann
 * @version $Id$
 */
@NoParams
public class DependencyPairsProcessor extends QTRSProcessor {

    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final ImmutableTriple<ImmutableSet<Rule>, ImmutableMap<FunctionSymbol, FunctionSymbol>, ImmutableMap<Rule, List<Pair<Position, Rule>>>> dps = qtrs.getDPs();
        final QDPProblem qdpProblem = QDPProblem.create(dps.x, qtrs, true);
        return ResultFactory.proved(qdpProblem, YNMImplication.EQUIVALENT, new DependencyPairsProof(qdpProblem, dps));
    }

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return true;
    }

    public static Proof createDPProof(final QDPProblem qdpProblem,
            final ImmutableTriple<ImmutableSet<Rule>, ImmutableMap<FunctionSymbol, FunctionSymbol>, ImmutableMap<Rule, List<Pair<Position, Rule>>>> dps) {
        return new DependencyPairsProof(qdpProblem, dps);
    }

    public static XMLMetaData adaptMetaData(
        final XMLMetaData xmlPreMetaData,
        final Map<FunctionSymbol, FunctionSymbol> tupleToDefined,
        final Set<FunctionSymbol> signature)
    {
        final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> labelMap = new HashMap<>();
        for (final FunctionSymbol f : signature) {
            final FunctionSymbol forig = tupleToDefined.get(f);
            if (forig == null) {
                labelMap.put(f, new Pair<>(f, FunctionSymbolAnnotator.EMPTY_ANNOTATOR));
            } else {
                labelMap.put(f, new Pair<>(forig, FunctionSymbolAnnotator.SHARP_ANNOTATOR));
            }
        }
        return new XMLMetaData(labelMap, xmlPreMetaData);
    }


    /**
     * Proof which prints out the resulting QDPProblem
     *
     * @author Matthias Sondermann
     * @version $Id$
     */
    private static class DependencyPairsProof extends QTRSProof {

        Map<Rule, List<Pair<Position,Rule>>> rulesToDPs;
        Map<FunctionSymbol, FunctionSymbol> definedToTuple;

        QDPProblem qdpProblem;

        private DependencyPairsProof(final QDPProblem qdpProblem,
                final ImmutableTriple<ImmutableSet<Rule>, ImmutableMap<FunctionSymbol, FunctionSymbol>, ImmutableMap<Rule, List<Pair<Position, Rule>>>> dps) {
            this.qdpProblem = qdpProblem;
            this.rulesToDPs = dps == null ? null : dps.z;
            this.definedToTuple = dps == null ? null : dps.y;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level){
            return "Using Dependency Pairs "+eu.cite(new Citation[]{Citation.AG00, Citation.LPAR04})+" we result in the following initial DP problem.";
        }

        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData xmlPreMetaData) {
            final Map<FunctionSymbol, FunctionSymbol> tupleToDefined = new HashMap<>();
            for (final Map.Entry<FunctionSymbol, FunctionSymbol> defToTup : this.definedToTuple.entrySet()) {
                tupleToDefined.put(defToTup.getValue(), defToTup.getKey());
            }
            return DependencyPairsProcessor.adaptMetaData(
                xmlPreMetaData,
                tupleToDefined,
                this.qdpProblem.getSignature());
        }


        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlPreMetaData, final CPFModus modus) {

            final XMLMetaData xmlMetaData = this.adaptMetaData(xmlPreMetaData);

            final Element markedSymbols = CPFTag.MARKED_SYMBOLS.create(doc,
                    doc.createTextNode("true"));
            final Element e = CPFTag.DP_TRANS.create(doc,
                    CPFTag.dps(doc, xmlMetaData, this.qdpProblem.getP()), markedSymbols, childrenProofs[0]);

            return (modus.isPositive() ? CPFTag.TRS_TERMINATION_PROOF : CPFTag.TRS_NONTERMINATION_PROOF).create(doc,e);
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }
}
