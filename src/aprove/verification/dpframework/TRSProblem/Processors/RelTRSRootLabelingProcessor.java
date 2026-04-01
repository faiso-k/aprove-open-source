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
 * Root labeling processor for relative TRSs
 *
 * @author Ulrich Schmidt-Goertz, Andreas Kelle-Emden
 * @version $Id$
 */
public class RelTRSRootLabelingProcessor extends RelTRSProcessor {

    /*
     * Which function symbols should get labeled?
     */
    protected final RootLabelingHeuristic heuristic;

    @ParamsViaArguments("Heuristic")
    public RelTRSRootLabelingProcessor(final RootLabelingHeuristic heuristic) {
        this.heuristic = heuristic;
    }

    @Override
    public boolean isRelTRSApplicable(final RelTRSProblem o) {
        return !FunctionSymbol.onlyConstants(o.getSignature());
    }

    @Override
    public Result processRelTRS(final RelTRSProblem problem, final Abortion aborter, final RuntimeInformation rti)
        throws AbortionException
    {

        final Set<Rule> r = problem.getR();
        final Set<Rule> s = problem.getS();
        final Set<Rule> rules = new LinkedHashSet<>(r);
        rules.addAll(s);

        // Root-Labeling is not applicable on a constant-only system
        final Set<FunctionSymbol> signature = problem.getSignature();

        // Check if every rule in R is root-preserving
        for (final Rule rule : rules) {
            final TRSFunctionApplication left = rule.getLeft();
            final TRSFunctionApplication right = (TRSFunctionApplication) rule.getRight();
            if (!left.getRootSymbol().equals(right.getRootSymbol())) {
                return ResultFactory.notApplicable("root labeling requires root-preserving rules");
            }
        }

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
                .notApplicable("root labeling with the given heuristic is not applicable on this problem");
        }

        final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap = new LinkedHashMap<>();
        // Now do the root labeling on the new set of rules
        final Set<Rule> newR = RootLabelingUtility.labelRules(r, signature, labelMap, aborter, xmlLabelMap);
        final Set<Rule> newS = RootLabelingUtility.labelRules(s, signature, labelMap, aborter, xmlLabelMap);

        // Create a new QTRS problem with empty Q
        final RelTRSProblem newRelTRS =
            RelTRSProblem.create(ImmutableCreator.create(newR), ImmutableCreator.create(newS));
        final Proof proof = new RootLabelingProof(newRelTRS, this.heuristic, labelMap, xmlLabelMap);

        return ResultFactory.proved(newRelTRS, YNMImplication.EQUIVALENT, proof);
    }

    /**
     * Proof which prints out the root labeling operations
     */
    private static class RootLabelingProof extends RelTRSProof {

        RelTRSProblem labelledTRS;
        RootLabelingHeuristic heuristic;
        Map<FunctionSymbol, Set<Integer>> labelMap;
        private final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap;


        private RootLabelingProof(
            final RelTRSProblem labelledTRS,
            final RootLabelingHeuristic heuristic,
            final Map<FunctionSymbol, Set<Integer>> labelMap,
            final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap)
        {
            this.labelledTRS = labelledTRS;
            this.heuristic = heuristic;
            this.labelMap = labelMap;
            this.xmlLabelMap = xmlLabelMap;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append("We used plain root labeling " + eu.cite(Citation.ROOTLAB) + " with the following heuristic:\n");
            s.append(this.heuristic.export(eu, this.labelMap));
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

                return CPFTag.RELATIVE_TERMINATION_PROOF.create(
                    doc,
                    CPFTag.SEMLAB.create(
                        doc,
                        CPFTag.MODEL.create(doc, CPFTag.ROOT_LABELING.create(doc)),
                        CPFTag.trs(doc, xmlMetaData, this.labelledTRS.getR()),
                        CPFTag.trs(doc, xmlMetaData, this.labelledTRS.getS()),
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
