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
import aprove.verification.dpframework.Heuristics.RootLabeling.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Rootlabeling processor for TRSs
 *
 * @author Andreas Kelle-Emden extracted flat cc by CKuknat
 */
public class RootLabelingProcessor extends QTRSProcessor {

    /*
     * Which function symbols should get labeled?
     */
    protected final RootLabelingHeuristic heuristic;
    protected final int threads;

    public static class Arguments {
        public RootLabelingHeuristic heuristic;
        public int threads = 1;
    }

    @ParamsViaArgumentObject
    public RootLabelingProcessor(final Arguments args) {
        this.heuristic = args.heuristic;
        this.threads = args.threads;
    }

    @Override
    public boolean isQTRSApplicable(final QTRSProblem o) {
        return !FunctionSymbol.onlyConstants(o.getRSignature());
    }

    /*
     * public Exportable getDescription(NameLength length) { return new
     * ExportableString("QTRS Root Labeling Processor"); }
     */

    @Override
    public Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti)
        throws AbortionException
    {
        Set<Rule> rules = qtrs.getR();

        // If Q is empty, root labeling is complete,
        // otherwise we can only guarantee soundness!
        final boolean qIsEmpty = qtrs.getQ().isEmpty();

        // Root-Labeling is not applicable on a constant-only system
        final Set<FunctionSymbol> signature = qtrs.getRSignature();

        // Check if every rule in R is root-preserving
        boolean isRootPreserving = true;
        for (final Rule rule : rules) {
            final TRSFunctionApplication left = rule.getLeft();
            final TRSFunctionApplication right = (TRSFunctionApplication) rule.getRight();
            if (!left.getRootSymbol().equals(right.getRootSymbol())) {
                isRootPreserving = false;
                break;
            }
        }

        final boolean isApplicable = isRootPreserving;

        // Apply root labelling, if applicable
        if (isApplicable) {

            // Try and run the given heuristic
            if (this.heuristic == null) {
                return ResultFactory.notApplicable("You need to specify an applicable heuristic");
            }
            if (!this.heuristic.isRLApplicable()) {
                return ResultFactory.notApplicable("the given heuristic is not applicable for plain root labeling");
            }
            final Map<FunctionSymbol, Set<Integer>> labelMap =
                this.heuristic.getLabelMap(rules, null, null, null, signature, null, null, 0);
            if (labelMap == null) {
                return ResultFactory
                    .notApplicable("root labeling with the given heuristic is not applicable on this DP problem");
            }

            final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap =
                new LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>>();
            // Now do the root labeling on the new set of rules
            rules = RootLabelingUtility.labelRules(rules, signature, labelMap, aborter, this.threads, xmlLabelMap);

            // Create a new QTRS problem with empty Q
            final QTRSProblem newQTRS = QTRSProblem.create(ImmutableCreator.create(rules));

            final Proof proof = new RootLabelingProof(newQTRS, qIsEmpty, this.heuristic, labelMap, xmlLabelMap, qtrs);

            return ResultFactory.proved(newQTRS, (qIsEmpty ? YNMImplication.EQUIVALENT : YNMImplication.SOUND), proof);
        }
        return ResultFactory.notApplicable("root labeling is not applicable here");
    }

    /**
     * Proof which prints out the root labeling operations
     */
    private static class RootLabelingProof extends QTRSProof {

        private final QTRSProblem labelledTRS;
        private final boolean qIsEmpty;
        private final RootLabelingHeuristic heuristic;
        private final Map<FunctionSymbol, Set<Integer>> labelMap;
        private final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap;
        private final QTRSProblem origObl;

        private RootLabelingProof(
            final QTRSProblem labelledTRS,
            final boolean qIsEmpty,
            final RootLabelingHeuristic heuristic,
            final Map<FunctionSymbol, Set<Integer>> labelMap,
            final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap,
            final QTRSProblem origObl)
        {
            this.labelledTRS = labelledTRS;
            this.qIsEmpty = qIsEmpty;
            this.heuristic = heuristic;
            this.labelMap = labelMap;
            this.xmlLabelMap = xmlLabelMap;
            this.origObl = origObl;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append("We used plain root labeling " + eu.cite(Citation.ROOTLAB) + " with the following heuristic:\n");
            s.append(this.heuristic.export(eu, this.labelMap));
            if (this.qIsEmpty) {
                s.append("As Q is empty the root labeling was sound AND complete.\n");
            }
            return s.toString();
        }

        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData preData) {
            return new XMLMetaData(this.xmlLabelMap, preData);
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData preData,
            final CPFModus modus)
        {

            final XMLMetaData xmlMetaData = this.adaptMetaData(preData);
            if (modus.isPositive()) {

                return CPFTag.TRS_TERMINATION_PROOF.create(
                    doc,
                    CPFTag.SEMLAB.create(
                        doc,
                        CPFTag.MODEL.create(doc, CPFTag.ROOT_LABELING.create(doc)),
                        CPFTag.trs(doc, xmlMetaData, this.labelledTRS.getR()),
                        childrenProofs[0]));
            } else {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
        }

    }
}
