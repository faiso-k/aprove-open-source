package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Heuristics.RootLabeling.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
import aprove.xml.*;
import immutables.*;

/**
 * Root-Labeling with Dependency Pairs, first transformation
 *
 * For the DP problem (P,R) the transformation returns the new DP problem
 * (block(P)_rl, FC_1(R)_rl)
 *
 * @author Andreas Kelle-Emden
 */
public class QDPRootLabelingFC1Processor extends Processor.ProcessorSkeleton {
    private static Logger log = Logger.getLogger("rootlab Logger");

    /*
     * Which function symbols should get labeled?
     */
    protected final RootLabelingHeuristic heuristic;
    protected final int threads;

    // be applicable to a QDP problem only if minimality will be retained?
    private final boolean preserveMinimality;

    @ParamsViaArgumentObject
    public QDPRootLabelingFC1Processor(Arguments args) {
        this.heuristic = args.heuristic;
        this.threads   = args.threads;
        this.preserveMinimality = args.preserveMinimality;
    }

    @Override
    public Result process(
        BasicObligation bobl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
    ) throws AbortionException {
        final QDPProblem qdp = (QDPProblem) bobl;
        Set<Rule> Rrules = qdp.getR();
        Set<Rule> Prules = qdp.getP();
        final QTermSet Q = qdp.getQ();

        final boolean qIsEmpty = Q.isEmpty();

        boolean isApplicable = true;

        // Collect symbols
        final Set<FunctionSymbol> symbolsF = new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> symbolsFHash = new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> symbolsFR = new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> symbolsFP = new LinkedHashSet<FunctionSymbol>();

        for (Rule rule : Rrules) {
            // FR is the set of all function symbols occurring in R
            symbolsFR.addAll(rule.getFunctionSymbols());
        }
        for (Rule rule : Prules) {
            // FHash is the set of all root symbols occurring in at least one lhs or rhs of the P-rules
            symbolsFHash.add(rule.getRootSymbol());
            final TRSTerm r = rule.getRight();
            if (r instanceof TRSFunctionApplication) {
                symbolsFHash.add(((TRSFunctionApplication)r).getRootSymbol());
            }
            // FP is the set of all function symbols occurring in P
            symbolsFP.addAll(rule.getFunctionSymbols());
        }
        // F is the set of all function symbols occurring in R or
        // in P without FHash
        symbolsF.addAll(symbolsFR);
        symbolsF.addAll(symbolsFP);
        symbolsF.removeAll(symbolsFHash);

        // Root-labeling is not applicable on constant-only systems
        boolean constantOnly = true;
        for (FunctionSymbol sym : symbolsF) {
            if (sym.getArity() > 0) {
                constantOnly = false;
                break;
            }
        }
        if (constantOnly) {
            QDPRootLabelingFC1Processor.log.log(
                Level.INFO,
                "QDPRootLabeling (FC1): not applicable on this constant-only system"
            );
            return ResultFactory.notApplicable("root labeling is not applicable on constant-only systems");
        }
        constantOnly = true;
        for (FunctionSymbol sym : symbolsFHash) {
            if (sym.getArity() > 0) {
                constantOnly = false;
                break;
            }
        }
        if (constantOnly) {
            QDPRootLabelingFC1Processor.log.log(
                Level.INFO,
                "QDPRootLabeling (FC1): not applicable on this constant-only system"
            );
            return ResultFactory.notApplicable("root labeling is not applicable on constant-only systems");
        }


        // Check if the DP problem is in the right form
        // i.e. root symbols of lhs or rhs of P-rules do neither
        // occur in R nor in subterms of P

        for (FunctionSymbol f : symbolsFHash) {
            if (symbolsFR.contains(f)) {
                isApplicable = false;
                QDPRootLabelingFC1Processor.log.log(
                    Level.INFO,
                    "QDPRootLabeling (FC1): not applicable, because the DP problem is not in the right form. (R "
                    + "contains a rootsymbol of P)"
                );
                break;
            }
            for (Rule p : Prules) {
                if (p.getLeft().getNonRootFunctionSymbols().contains(f)) {
                    isApplicable = false;
                    QDPRootLabelingFC1Processor.log.log(
                        Level.INFO,
                        "QDPRootLabeling (FC1): not applicable, because the DP problem is not in the right form. (A "
                        + "subterm of P contains a rootsymbol of P)"
                    );
                    break;
                }
                if (p.getRight() instanceof TRSFunctionApplication) {
                    if (((TRSFunctionApplication)p.getRight()).getNonRootFunctionSymbols().contains(f)) {
                        isApplicable = false;
                        QDPRootLabelingFC1Processor.log.log(
                            Level.INFO,
                            "QDPRootLabeling (FC1): not applicable, because the DP problem is not in the right form. "
                            + "(A subterm of P contains a rootsymbol of P)"
                        );
                        break;
                    }
                }
            }
        }


        if (!isApplicable) {
            return ResultFactory.notApplicable("root labeling is not applicable here");
        }

        // New function symbol DELTA with arity 1 for the block function
        String delta_name = "DELTA";
        FunctionSymbol symbol_delta = FunctionSymbol.create(delta_name, 1);
        while (symbolsFR.contains(symbol_delta) || symbolsFP.contains(symbol_delta)) {
            // DELTA is already known - try next name
            // R and P are finite, for that reason finding a new function symbol will terminate in finite time
            delta_name = "_" + delta_name;
            symbol_delta = FunctionSymbol.create(delta_name, 1);
        }

        final Set<FunctionSymbol> labelSymbols = new LinkedHashSet<FunctionSymbol>(symbolsF);
        symbolsF.add(symbol_delta);

        // Try and run the given heuristic
        if (this.heuristic == null) {
            return ResultFactory.notApplicable("You need to specify an applicable heuristic");
        }
        if (!this.heuristic.isFC1Applicable()) {
            return ResultFactory.notApplicable("the given heuristic is not applicable for FC1 root labeling");
        }
        final Map<FunctionSymbol, Set<Integer>> labelMap =
            this.heuristic.getLabelMap(Rrules, Prules, symbolsF, symbolsFHash, symbolsFR, symbolsFP, symbol_delta, 1);
        if (labelMap == null) {
            return
                ResultFactory.notApplicable(
                    "root labeling with the given heuristic is not applicable on this DP problem"
                );
        }

        final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap =
            new LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>>();

        // we need fresh names for the variables in the flat contexts
        @SuppressWarnings("unchecked")
        final Set<TRSVariable> varNames =
            (Set<TRSVariable>)aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(Rrules);
        final NameGenerator ng = new AppendNameGenerator(0, 0);
        final FreshNameGenerator fng = new FreshNameGenerator(varNames, ng);

        // Now build flat contexts for R with respect to DELTA
        final LinkedList<Context> flatContexts = new LinkedList<Context>();
        Rrules = RootLabelingUtility.flatContext(Rrules, symbolsF, aborter,
                flatContexts, fng);

        if (!flatContexts.isEmpty()) {
            // Build block(P)
            Prules = RootLabelingUtility.block(Prules, symbol_delta, aborter);
        }

        final boolean flatMinimality = qdp.getMinimal() &&
        aprove.verification.dpframework.BasicStructures.CollectionUtils.isLeftLinear(qdp.getR());
        final QTRSProblem flatQTRS = QTRSProblem.create(ImmutableCreator.create(Rrules));
        final QDPProblem flatQDP = QDPProblem.create(Prules, flatQTRS, flatMinimality);

        // Label block(P)
        Prules = RootLabelingUtility.labelRules(Prules, labelSymbols, labelMap,
                aborter, this.threads, xmlLabelMap);

        // and finally, label FC_1(R)
        Rrules = RootLabelingUtility.labelRules(Rrules, labelSymbols, labelMap, aborter, this.threads, xmlLabelMap);


        // We made it, now build the proof
        // New QDP has empty Q
        final QTRSProblem newQTRS = QTRSProblem.create(ImmutableCreator.create(Rrules));

        final boolean newMinimality = qdp.getMinimal() &&
            aprove.verification.dpframework.BasicStructures.CollectionUtils.isLeftLinear(qdp.getR());
        final QDPProblem newQDP = QDPProblem.create(Prules, newQTRS, newMinimality);
        final RootLabelingFC1Proof proof = new RootLabelingFC1Proof(newQDP, qIsEmpty,
                this.heuristic, labelMap, flatQDP, qdp, xmlLabelMap, flatContexts,
                symbol_delta);

        return ResultFactory.proved(newQDP, (qIsEmpty?YNMImplication.EQUIVALENT:YNMImplication.SOUND), proof);
    }

    /**
     * For now we require at least one of not enforcing preservation of
     * minimality, left-linearity of R or non-minimality.
     * Details: Sternagel, Thiemann, CSL'10.
     */
    @Override
    public boolean isApplicable(BasicObligation o) {
        if (Options.certifier.isCeta()) {
            return false; // CeTA only supports FC2
        }
        if (! (o instanceof QDPProblem)) {
            return false;
        }
        final QDPProblem qdp = (QDPProblem) o;
        return (! qdp.getP().isEmpty()) &&
            (!this.preserveMinimality || !qdp.getMinimal() ||
            aprove.verification.dpframework.BasicStructures.CollectionUtils.isLeftLinear(qdp.getR()));
    }

    /**
     * Proof which prints out the root labeling operations
     */
    private class RootLabelingFC1Proof extends QDPProof {

        boolean qIsEmpty;
        private final QDPProblem origObl;
        private final QDPProblem flatObl;
        private final QDPProblem labelledQDP;
        RootLabelingHeuristic heuristic;
        private final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap;
        private final Map<FunctionSymbol, Set<Integer>> labelMap;
        private final Collection<Context> flatContexts;
        private final FunctionSymbol freshOne;

        private RootLabelingFC1Proof(
            QDPProblem labelledQDP,
            boolean qIsEmpty,
            RootLabelingHeuristic heuristic,
            Map<FunctionSymbol,
            Set<Integer>> labelMap,
            QDPProblem flatObl,
            QDPProblem origObl,
            Map<FunctionSymbol,
            Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap,
            Collection<Context> flatContexts,
            FunctionSymbol freshOne
        ) {
            this.labelledQDP = labelledQDP;
            this.qIsEmpty = qIsEmpty;
            this.heuristic   = heuristic;
            this.labelMap    = labelMap;
            this.origObl = origObl;
            this.flatObl = flatObl;
            this.xmlLabelMap = xmlLabelMap;
            this.flatContexts = flatContexts;
            this.freshOne = freshOne;
        }

        @Override
        public String export(Export_Util eu, VerbosityLevel level){
            final StringBuilder s = new StringBuilder();
            s.append("We used root labeling (first transformation) "+eu.cite(Citation.ROOTLAB)+" with the following heuristic:\n");
            s.append(this.heuristic.export(eu, this.labelMap));
            if (this.qIsEmpty) {
                s.append("As Q is empty the root labeling was sound AND complete.\n");
            }
            return s.toString();
        }

        @Override
        public XMLMetaData adaptMetaData(XMLMetaData preData) {
            return new XMLMetaData(this.xmlLabelMap, preData);
        }

    }

    public static class Arguments {
        public RootLabelingHeuristic heuristic;
        public int threads = 1;
        public boolean preserveMinimality = true;
    }
}
