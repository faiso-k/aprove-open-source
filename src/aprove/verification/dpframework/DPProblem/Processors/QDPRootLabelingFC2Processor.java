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
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
import immutables.*;

/**
 * Root-Labeling with Dependency Pairs, second transformation
 *
 *
 * @author Andreas Kelle-Emden
 */
public class QDPRootLabelingFC2Processor extends Processor.ProcessorSkeleton {
    private static final Logger log = Logger.getLogger("rootlab Logger");

    /*
     * Which function symbols should get labeled?
     */
    protected final RootLabelingHeuristic heuristic;
    protected final int threads;

    // be applicable to a QDP problem only if minimality will be retained?
    private final boolean preserveMinimality;

    @ParamsViaArgumentObject
    public QDPRootLabelingFC2Processor(final Arguments args) {
        this.heuristic = args.heuristic;
        this.threads   = args.threads;
        this.preserveMinimality = args.preserveMinimality;
    }

    @SuppressWarnings("unchecked")
    @Override
    public Result process(final BasicObligation bobl, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti)
                throws AbortionException {
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

        for (final Rule rule : Rrules) {
            // FR is the set of all function symbols occurring in R
            symbolsFR.addAll(rule.getFunctionSymbols());
        }
        for (final Rule rule : Prules) {
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
        // in P without FHash, FAll contains all function symbols
        symbolsF.addAll(symbolsFR);
        symbolsF.addAll(symbolsFP);
        symbolsF.removeAll(symbolsFHash);

        // Root-labeling is not applicable on constant-only systems
        boolean constantOnly = true;
        for (final FunctionSymbol sym : symbolsF) {
            if (sym.getArity() > 0) {
                constantOnly = false;
                break;
            }
        }
        if (constantOnly) {
            QDPRootLabelingFC2Processor.log.log(Level.INFO, "QDPRootLabeling (FC2): not applicable on this constant-only system");
            return ResultFactory.notApplicable("root labeling is not applicable on constant-only systems");
        }
        constantOnly = true;
        for (final FunctionSymbol sym : symbolsFHash) {
            if (sym.getArity() > 0) {
                constantOnly = false;
                break;
            }
        }
        if (constantOnly) {
            QDPRootLabelingFC2Processor.log.log(Level.INFO, "QDPRootLabeling (FC2): not applicable on this constant-only system");
            return ResultFactory.notApplicable("root labeling is not applicable on constant-only systems");
        }


        // Check if the DP problem is in the right form
        // i.e. root symbols of lhs or rhs of P-rules do neither
        // occur in R nor in subterms of P

        for (final FunctionSymbol f : symbolsFHash) {
            if (symbolsFR.contains(f)) {
                isApplicable = false;
                QDPRootLabelingFC2Processor.log.log(Level.INFO, "QDPRootLabeling (FC2): not applicable, because the DP problem is not in the right form. (R contains a rootsymbol of P)");
                break;
            }
            for (final Rule p : Prules) {
                if (p.getLeft().getNonRootFunctionSymbols().contains(f)) {
                    isApplicable = false;
                    QDPRootLabelingFC2Processor.log.log(Level.INFO, "QDPRootLabeling (FC2): not applicable, because the DP problem is not in the right form. (A subterm of P contains a rootsymbol of P)");
                    break;
                }
                if (p.getRight() instanceof TRSFunctionApplication) {
                    if (((TRSFunctionApplication)p.getRight()).getNonRootFunctionSymbols().contains(f)) {
                        isApplicable = false;
                        QDPRootLabelingFC2Processor.log.log(Level.INFO, "QDPRootLabeling (FC2): not applicable, because the DP problem is not in the right form. (A subterm of P contains a rootsymbol of P)");
                        break;
                    }
                }
            }
        }


        if (!isApplicable) {
            return ResultFactory.notApplicable("root labeling is not applicable here");
        }

        // Try and run the given heuristic
        if (this.heuristic == null) {
            return ResultFactory.notApplicable("You need to specify an applicable heuristic");
        }
        if (!this.heuristic.isFC2Applicable()) {
            return ResultFactory.notApplicable("the given heuristic is not applicable for FC2 root labeling");
        }
        final Map<FunctionSymbol, Set<Integer>> labelMap = this.heuristic.getLabelMap(Rrules, Prules, symbolsF, symbolsFHash, symbolsFR, symbolsFP, null, 2);
        if (labelMap == null) {
            QDPRootLabelingFC2Processor.log.log(Level.INFO, "QDPRootLabeling (FC2): not applicable on this DP problem with the given heuristic");
            return ResultFactory.notApplicable("root labeling with the given heuristic is not applicable on this DP problem");
        }

        // Build R_a (root altering rules in R)
        Set<Rule> rootAltering = new LinkedHashSet<Rule>();
        for (final Rule rule: Rrules) {
            final TRSTerm rhs = rule.getRight();
            if (rhs instanceof TRSFunctionApplication) {
                if (!((TRSFunctionApplication)rhs).getRootSymbol().equals(rule.getLeft().getRootSymbol())) {
                    rootAltering.add(rule);
                }
            } else {
                rootAltering.add(rule);
            }
        }

        // we need fresh names for the variables in the flat contexts
        final Set<TRSVariable> varNames =
            (Set<TRSVariable>)aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(Rrules);
        varNames.addAll((Set<TRSVariable>)aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(Prules));
        final NameGenerator ng = new AppendNameGenerator(0, 0);
        final FreshNameGenerator fng = new FreshNameGenerator(varNames, ng);

        // Build flat contexts of R_a w.r.t. FHash
        rootAltering = RootLabelingUtility.flatContext(rootAltering, symbolsFHash, aborter, null, fng);

        // Build flat contexts of R w.r.t. F
        Rrules = RootLabelingUtility.flatContext(Rrules, symbolsF, aborter, null, fng);

        final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap = new LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>>();
        // Label P w.r.t. all function symbols
        Prules = RootLabelingUtility.labelRules(Prules, symbolsF, labelMap, aborter, this.threads, xmlLabelMap);

        // Label FC(R_a)
        rootAltering = RootLabelingUtility.labelRules(rootAltering, symbolsF, labelMap, aborter, this.threads, xmlLabelMap);

        // Label FC(R)
        Rrules = RootLabelingUtility.labelRules(Rrules, symbolsF, labelMap, aborter, this.threads, xmlLabelMap);

        // Unite P_rl with FC(R_a)_rl
        Prules.addAll(rootAltering);


        // We made it, now build the proof
        // New QDP has empty Q
        final QTRSProblem newQTRS = QTRSProblem.create(ImmutableCreator.create(Rrules));

        final boolean newMinimality = qdp.getMinimal() &&
            aprove.verification.dpframework.BasicStructures.CollectionUtils.isLeftLinear(qdp.getR());
        final QDPProblem newQDP = QDPProblem.create(Prules, newQTRS, newMinimality);
        final RootLabelingFC2Proof proof = new RootLabelingFC2Proof(qdp, newQDP, qIsEmpty, this.heuristic, labelMap);

        return ResultFactory.proved(newQDP, (qIsEmpty?YNMImplication.EQUIVALENT:YNMImplication.SOUND), proof);
    }

    /**
     * For now we require at least one of not enforcing preservation of
     * minimality, left-linearity of R or non-minimality.
     * Details: Sternagel, Thiemann, CSL'10.
     */
    @Override
    public boolean isApplicable(final BasicObligation o) {
        if (Options.certifier.isCeta()) {
            return false;
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
    private class RootLabelingFC2Proof extends QDPProof {

        boolean qIsEmpty;
        QDPProblem labelledQDP;
        QDPProblem origQDP;
        RootLabelingHeuristic heuristic;
        Map<FunctionSymbol, Set<Integer>> labelMap;

        private RootLabelingFC2Proof(final QDPProblem origQDP, final QDPProblem labelledQDP, final boolean qIsEmpty, final RootLabelingHeuristic heuristic, final Map<FunctionSymbol, Set<Integer>> labelMap) {
            this.origQDP     = origQDP;
            this.labelledQDP = labelledQDP;
            this.qIsEmpty    = qIsEmpty;
            this.heuristic   = heuristic;
            this.labelMap    = labelMap;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level){
            final StringBuilder s = new StringBuilder();
            s.append("We used root labeling (second transformation) "+eu.cite(Citation.ROOTLAB)+" with the following heuristic:" + eu.newline());
            s.append(this.heuristic.export(eu, this.labelMap));
            if (this.qIsEmpty) {
                s.append("As Q is empty the root labeling was sound AND complete." + eu.newline());
            }
            return s.toString();
        }

    }

    public static class Arguments {
        public RootLabelingHeuristic heuristic;
        public int threads = 1;
        public boolean preserveMinimality = true;
    }
}
