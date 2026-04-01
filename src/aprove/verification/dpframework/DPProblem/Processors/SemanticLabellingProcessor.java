package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Rewriting.SemanticLabelling.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.xml.*;
import immutables.*;

/**
 * Semantic Labelling Processor for QDP Problems.
 *
 * @author thiemann
 */

public class SemanticLabellingProcessor extends Processor.ProcessorSkeleton {

    private final static Logger log = Logger.getLogger("semlab Logger");

    /**
     * An <code>int</code> containing the size of the carrier set of possible
     * models.
     */
    private final int carrierSetSize;

    /**
     * Denote whether to use Boolean Tuples as the carrier. In this case the
     * PolynomialFunctionRepresentation will not be used.
     */
    private final boolean useBooleanTuples;

    private final boolean allowQuasi;

    /**
     * Always find (real) quasi models, useful for Boolean Tuples.
     */
    private final boolean enforceQuasi;

    private final UserStrategy strategy;

    /**
     * The (SAT) engine that will be used to check for effectiveness.
     */
    private final Engine engine;

    /**
     * The (incremental SAT) engine that will be used to find models using
     * Boolean Tuples.
     */
    private final Engine incrementalEngine;

    /**
     * The dimension of the Boolean Tuples (if used).
     */
    private final int dimension;

    @ParamsViaArgumentObject
    public SemanticLabellingProcessor(final Arguments arguments) {
        this.allowQuasi = arguments.allowQuasi;
        this.enforceQuasi = arguments.enforceQuasi;
        this.dimension = arguments.dimension;
        this.useBooleanTuples = arguments.booleanTuples;
        if (this.useBooleanTuples) {
            if (this.dimension > 30 || this.dimension < 1) {
                throw new IllegalArgumentException("Unsupported dimension "
                    + this.dimension
                    + "! Use a dimension between 1 and 30.");
            } else {
                this.carrierSetSize = 1 << this.dimension;
            }
        } else {
            this.carrierSetSize = arguments.carrierSetSize;
        }
        this.engine = arguments.engine;
        this.incrementalEngine = arguments.incrementalEngine;
        this.strategy = new VariableStrategy(arguments.strategy);
    }

    @Override
    public boolean isApplicable(final BasicObligation o) {
        return (o instanceof QDPProblem) && (!((QDPProblem) o).getP().isEmpty());
    }

    @Override
    public Result process(
        final BasicObligation bobl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        final QDPProblem qdp = (QDPProblem) bobl;
        final Set<Rule> rRules = qdp.getR();
        final Set<Rule> pRules = qdp.getP();
        final int totalSize = rRules.size() + pRules.size();
        final QTermSet qTerms = qdp.getQ();
        final boolean emptyQ = qTerms.isEmpty();
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap =
            new LinkedHashMap<>();

        Set<Rule> decrR = null;
        Map<FunctionSymbol, FunctionSymbol> decrRoriginMap = new LinkedHashMap<>();

        boolean linearQ = true;
        for (final TRSTerm t : qTerms.getTerms()) {
            if (!t.isLinear()) {
                linearQ = false;
                break;
            }
        }

        Set<FunctionSymbol> requiredInterpretations;
        Set<FunctionSymbol> irrelevantSymbols;
        final Set<FunctionSymbol> headSymbols = qdp.getHeadSymbols();
        final Set<FunctionSymbol> prNoHeadSymbols = new LinkedHashSet<>(qdp.getPRSignature());
        prNoHeadSymbols.removeAll(headSymbols);
        if (emptyQ) {
            irrelevantSymbols = headSymbols;
            requiredInterpretations = prNoHeadSymbols;
        } else {
            requiredInterpretations = prNoHeadSymbols;
            irrelevantSymbols = new LinkedHashSet<>(qdp.getSignature());
            irrelevantSymbols.removeAll(requiredInterpretations);
        }

        // use this iterator to check all models
        final Iterator<Pair<Boolean, Labeller>> iter;
        if (this.useBooleanTuples) {
            final Triple<Engine, Integer, Abortion> btInformation =
                new Triple<>(this.incrementalEngine, this.dimension, aborter);
            iter =
                Model.getModelIterator(
                    rRules,
                    requiredInterpretations,
                    irrelevantSymbols,
                    new BooleanTupleFunctionRepresentation(this.carrierSetSize),
                    this.allowQuasi,
                    this.enforceQuasi,
                    btInformation);
        } else {
            // RT: Note that C. Hangs PolyomialFunctionRepresentation will only
            // generate polys with interpretations that can be expressed with
            // CarrierSetSize 2. So do not wonder that constant 2 or something
            // like that is not generated if you choose CarrierSetSize 3.
            iter =
                Model.getModelIterator(
                    rRules,
                    requiredInterpretations,
                    irrelevantSymbols,
                    new PolynomialFunctionRepresentation(this.carrierSetSize),
                    this.allowQuasi,
                    false,
                    null);
        }

        int dropped = 0;
        int count = 0;

        while (iter.hasNext()) {
            count++;
            final Pair<Boolean, Labeller> o = iter.next();
            final Labeller l = o.y;

            // build labelled rules
            int newRsize = 0;
            final Collection<Pair<Rule, Collection<Rule>>> labelledR = new ArrayList<>(rRules.size());
            for (final Rule rule : rRules) {
                final Collection<Rule> labelledRules = new ArrayList<>();
                l.addLabeled(rule, labelledRules, xmlLabelMap);
                newRsize += labelledRules.size();
                labelledR.add(new Pair<>(rule, labelledRules));
            }

            // and labelled pairs
            final boolean quasi = o.x;
            final Map<Rule, Collection<Rule>> labelledP = new LinkedHashMap<>(pRules.size());
            for (final Rule rule : pRules) {
                final Collection<Rule> labelledRules = new ArrayList<>();
                if (quasi) {
                    l.addQuasiLabeledPairs(rule, labelledRules, headSymbols, xmlLabelMap);
                } else {
                    l.addLabeled(rule, labelledRules, xmlLabelMap);
                }
                labelledP.put(rule, labelledRules);
            }

            // check effective labelling
            final List<Pair<Rule, Collection<Rule>>> allRules = new ArrayList<>(rRules.size() + pRules.size());
            allRules.addAll(labelledR);
            for (final Map.Entry<Rule, Collection<Rule>> pairLabpairs : labelledP.entrySet()) {
                allRules.add(new Pair<>(pairLabpairs.getKey(), pairLabpairs.getValue()));
            }
            if (Labeller.EffectiveChecker.checkIneffective(allRules, l, this.engine, aborter)) {
                dropped++;
                continue;
            }

            // create labelled TRS
            final Set<Rule> newR = new LinkedHashSet<>(newRsize);
            for (final Pair<Rule, Collection<Rule>> labelledRules : labelledR) {
                newR.addAll(labelledRules.y);
            }

            // create labelled graph

            // to build the new graph note that it may be the case that there
            // are different nodes in the QDP-P-component with the same rule.
            final Graph<Rule, ?> newP = new Graph<>();
            final Graph<Rule, ?> previousGraph = qdp.getDependencyGraph().getGraph();
            final Set<Node<Rule>> previousP = previousGraph.getNodes();
            final Map<Node<Rule>, Collection<Node<Rule>>> oldDpToNewDPs = new HashMap<>(previousP.size());
            // now create for each node (and not only for each rule, see above)
            // a corresponding set of new nodes with labeled rules
            for (final Node<Rule> dp : previousP) {
                final Rule rule = dp.getObject();
                final Collection<Rule> newRules = labelledP.get(rule);
                final Collection<Node<Rule>> newDPs = new ArrayList<>(newRules.size());
                for (final Rule newRule : newRules) {
                    newDPs.add(new Node<>(newRule));
                }
                oldDpToNewDPs.put(dp, newDPs);
            }
            // afterwards create edges
            for (final Edge<?, Rule> edge : previousGraph.getEdges()) {
                for (final Node<Rule> start : oldDpToNewDPs.get(edge.getStartNode())) {
                    for (final Node<Rule> end : oldDpToNewDPs.get(edge.getEndNode())) {
                        newP.addEdge(start, end);
                    }
                }
            }

            for (final Collection<Node<Rule>> newRuleNodes : oldDpToNewDPs.values()) {
                for (final Node<Rule> newRuleNode : newRuleNodes) {
                    newP.addNode(newRuleNode);
                }
            }

            SemanticLabellingProcessor.log.log(Level.FINE, "Checking " + (quasi ? "quasi-" : "") + "model: {0}\n", l);

            boolean newMinimal = qdp.getMinimal();
            if (quasi) {
                // the decr rules are independent of the labeling (they depend
                // on the carrierSetSize and the signature) and hence can be
                // reused
                if (decrR == null) {
                    // because the labelToOriginMap is contained in the labeler
                    // which is replaced after every model, the decrR
                    // information has to be stored separately.

                    // backup the map before adding information for the decrR.
                    final Map<FunctionSymbol, FunctionSymbol> backup = new LinkedHashMap<>(l.getLabelToOriginMap());
                    l.getLabelToOriginMap().clear();

                    // get decrR (and fill the map)
                    decrR = l.getDecreasingRules(prNoHeadSymbols, xmlLabelMap);

                    // get the map information about decrR.
                    decrRoriginMap = new LinkedHashMap<>(l.getLabelToOriginMap());

                    // restore the map, but keep new information
                    final Map<FunctionSymbol, FunctionSymbol> labelToOriginMap = l.getLabelToOriginMap();
                    for (final Map.Entry<FunctionSymbol, FunctionSymbol> entry : backup.entrySet()) {
                        labelToOriginMap.put(entry.getKey(), entry.getValue());
                    }
                } else {
                    final Map<FunctionSymbol, FunctionSymbol> labelToOriginMap = l.getLabelToOriginMap();
                    for (final Map.Entry<FunctionSymbol, FunctionSymbol> entry : decrRoriginMap.entrySet()) {
                        labelToOriginMap.put(entry.getKey(), entry.getValue());
                    }
                }
                newR.addAll(decrR);

                if (!emptyQ && !linearQ) {
                    newMinimal = false;
                }
            }

            QTRSProblem newQTRS;
            if (emptyQ) {
                newQTRS = QTRSProblem.create(ImmutableCreator.create(newR));
            } else if (!quasi) {
                final Set<TRSFunctionApplication> newQterms = new LinkedHashSet<>();
                for (final TRSFunctionApplication q : qTerms.getTerms()) {
                    l.addLabeled(q, newQterms, xmlLabelMap);
                }
                newQTRS = QTRSProblem.create(ImmutableCreator.create(newR), newQterms);
            } else {
                final Set<TRSFunctionApplication> newQterms = new LinkedHashSet<>();
                final Collection<FunctionSymbol> functionSymbols = new LinkedHashSet<>();
                final Set<TRSTerm> todoSet = new LinkedHashSet<>();
                for (final TRSFunctionApplication q : qTerms.getTerms()) {
                    for (final TRSTerm subTerm : q.getSubTerms()) {
                        todoSet.add(subTerm);
                        if (subTerm instanceof TRSFunctionApplication) {
                            functionSymbols.add(((TRSFunctionApplication) subTerm).getRootSymbol());
                        }
                    }
                }
                final CollectionMap<FunctionSymbol, FunctionSymbol> labelledFS = new CollectionMap<>();
                for (final FunctionSymbol funcSym : functionSymbols) {
                    final Collection<FunctionSymbol> labelledFuncSyms = l.labelFS(funcSym, xmlLabelMap);
                    labelledFS.add(funcSym, labelledFuncSyms);
                }

                final CollectionMap<TRSTerm, TRSTerm> map = new CollectionMap<>();

                final LinkedList<TRSTerm> todo = new LinkedList<>(todoSet);
                WHILE: while (!todo.isEmpty()) {
                    final TRSTerm term = todo.poll();
                    if (term.isVariable()) {
                        map.add(term, term);
                    } else {
                        assert (term instanceof TRSFunctionApplication);
                        final TRSFunctionApplication fa = (TRSFunctionApplication) term;
                        final FunctionSymbol fs = fa.getRootSymbol();
                        if (fa.isConstant()) {
                            for (final FunctionSymbol labFs : labelledFS.get(fs)) {
                                final TRSFunctionApplication labFa = TRSTerm.createFunctionApplication(labFs);
                                map.add(fa, labFa);
                            }
                        } else {
                            final List<Collection<TRSTerm>> labArgs = new LinkedList<>();
                            for (final TRSTerm sub : fa.getArguments()) {
                                if (!map.containsKey(sub)) {
                                    todo.offer(term);
                                    continue WHILE;
                                }
                                labArgs.add(map.get(sub));
                            }
                            final ListGenerator<TRSTerm> lg = new ListGenerator<>(labArgs, true);
                            while (lg.hasNext()) {
                                final ArrayList<? extends TRSTerm> choice = lg.next();
                                for (final FunctionSymbol labFs : labelledFS.get(fa.getRootSymbol())) {
                                    final TRSFunctionApplication labFa = TRSTerm.createFunctionApplication(labFs, choice);
                                    map.add(fa, labFa);
                                }
                            }
                        }

                    }
                }
                for (final TRSTerm qTerm : qTerms.getTerms()) {
                    for (final TRSTerm labelledqTerm : map.get(qTerm)) {
                        newQterms.add((TRSFunctionApplication) labelledqTerm);
                    }
                }

                newQTRS = QTRSProblem.create(ImmutableCreator.create(newR), newQterms);
            }

            // create labelled QDPProblem
            final QDPProblem labelledQDP = QDPProblem.create(newP, newQTRS, newMinimal);

            final BasicObligationNode labelledQDPNode = new BasicObligationNode(labelledQDP);

            final StrategyExecutionHandle handle =
                Machine.theMachine.startSubMachine(
                    this.strategy,
                    rti.getProgram(),
                    labelledQDPNode,
                    null,
                    aborter.getClocks(),
                    false);

            HandleChecker.check(handle, aborter);

            // okay, we have the result after the strategy
            final ExecutableStrategy result = handle.getResult();
            if (result == null || result.isFail()) {
                // we have not performed one simplification step, so
                continue;
                // unlabelling will result in the original TRS.
            } else {
                Set<Rule> finalRRules;
                Set<Rule> finalPRules;
                final List<BasicObligationNode> newProblems = ((Success) result).getPositions();
                if (newProblems.isEmpty()) {
                    // hooray, we have proven it completely.
                    finalRRules = null;
                    finalPRules = null;
                } else {
                    // collect new P and R
                    finalRRules = new LinkedHashSet<>(rRules.size());
                    finalPRules = new LinkedHashSet<>(pRules.size());
                    for (final BasicObligationNode resOblNode : newProblems) {
                        final QDPProblem labelledQDPAfterProc = (QDPProblem) resOblNode.getBasicObligation();
                        for (final Rule rule : labelledQDPAfterProc.getR()) {
                            if (!newR.contains(rule)) {
                                if (Globals.useAssertions) {
                                    assert (false) : "semlab used with rule " + "modifying processor";
                                } else {
                                    return ResultFactory.unsuccessful("semlab was invoked with a "
                                        + "strategy changing rules!");
                                }
                            }
                            finalRRules.add(l.unlabel(rule));
                        }
                        for (final Rule rule : labelledQDPAfterProc.getP()) {
                            if (!newP.getNodeObjects().contains(rule)) {
                                if (Globals.useAssertions) {
                                    assert (false) : "semlab used with rule " + "modifying processor";
                                } else {
                                    return ResultFactory.unsuccessful("semlab was invoked with a "
                                        + "strategy changing rules!");
                                }
                            }
                            finalPRules.add(l.unlabel(rule));
                        }
                    }

                    // to get rid of unlabelled decr rules
                    if (quasi) {
                        finalRRules.retainAll(rRules);
                    }
                    if (finalRRules.size() + finalPRules.size() == totalSize) {
                        // we have gained nothing
                        continue;
                    }
                }

                // okay, we have successfully applied semlab.
                // now build final result
                SemanticLabellingProcessor.log.log(Level.INFO, "\n\nDropped " + dropped + " of " + count + " models by effective labelling\n\n\n");
                final boolean completelySolved = finalRRules == null;
                final Proof proof =
                    new SemLabProof(labelledQDP, quasi, l, xmlLabelMap, qdp, this.carrierSetSize, completelySolved);
                if (completelySolved) {
                    assert (finalPRules == null);
                    labelledQDPNode.recursiveRepropagateTruthValues();
                    final ExecutableStrategy succStrategy = Success.EMPTY;
                    return ResultFactory.provedWithNewStrategy(
                        labelledQDPNode,
                        YNMImplication.SOUND,
                        proof,
                        succStrategy);
                } else {
                    final QDPProblem finalQDP = qdp.getSubProblem(finalPRules, ImmutableCreator.create(finalRRules));
                    // create a copy of qdp with a possibly different truth
                    // value
                    final BasicObligationNode relativeNode =
                        new BasicObligationNode(qdp.getSameProblem(qdp.getMinimal()));
                    final ObligationNodeChild relativeChild =
                        new ObligationNodeChild(labelledQDPNode, proof, YNMImplication.SOUND);
                    relativeNode.addTechnique(relativeChild, false);
                    final Processor proc = new QDPSplitProcessor(relativeNode, newProblems, finalQDP);
                    final ExecutableStrategy exStr =
                        new ExecProcessorStrategy(proc, oblNode, rti, "SemLabUtil", "<internal>");
                    return ResultFactory.justANewStrategy(exStr);
                }
            }
        } // end of model-iteration

        SemanticLabellingProcessor.log.log(Level.CONFIG, "Dropped " + dropped + " of " + count + " models by effective labelling\n");

        return ResultFactory.unsuccessful();
    }

    /**
     * Proof which prints out the resulting QDPProblem.
     */
    private static class SemLabProof extends QDPProof {

        private final QDPProblem labelledQDP;
        private final boolean quasi;
        private final Labeller labeller;
        private final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap;
        private final QDPProblem origObl;
        private final int carrierSize;
        private final boolean requireOnlineCertification;

        private SemLabProof(
            final QDPProblem labelledQDP,
            final boolean quasi,
            final Labeller labeller,
            final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap,
            final QDPProblem origObl,
            final int carrierSize,
            final boolean requireOnlineCertification)
        {
            this.labelledQDP = labelledQDP;
            this.quasi = quasi;
            this.labeller = labeller;
            this.xmlLabelMap = xmlLabelMap;
            this.origObl = origObl;
            this.carrierSize = carrierSize;
            this.requireOnlineCertification = requireOnlineCertification;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append("We found the following "
                + (this.quasi ? "quasi-" : "")
                + "model for the rules of the TRSs R and P.\n");
            s.append(this.labeller.export(eu));
            s.append("By semantic labelling "
                + eu.cite(Citation.SEMLAB)
                + " we obtain the following labelled QDP problem.");
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

            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, preData, modus);
            }
            final XMLMetaData xmlMetaData = this.adaptMetaData(preData);
            final Element semanticLabeling =
                CPFTag.SEMLAB_PROC.create(
                    doc,
                    CPFTag.MODEL.create(doc, this.labeller.toCPF(doc, preData, this.carrierSize, this.quasi)),
                    CPFTag.dps(doc, xmlMetaData, this.labelledQDP.getP()),
                    CPFTag.trs(doc, xmlMetaData, this.labelledQDP.getR()));

            if (this.labelledQDP.getQ().getTerms().size() > 0) {
                semanticLabeling.appendChild(this.labelledQDP.getQ().toCPF(doc, xmlMetaData));
            }

            semanticLabeling.appendChild(childrenProofs[0]);

            return CPFTag.DP_PROOF.create(doc, semanticLabeling);
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive() && this.labeller.isCPFSupported() == null;
        }

        @Override
        public String getNonCPFExportableReason(final CPFModus modus) {
            final String err = this.labeller.isCPFSupported();
            return super.getNonCPFExportableReason(modus) + (err != null ? "Semlab + " + err : "Semlab for disproving");
        }

        @Override
        public boolean requireFullSubproof(final CPFModus modus, final int i) {
            return this.requireOnlineCertification;
        }

    }

    public static class Arguments {
        public boolean allowQuasi = true;
        public boolean booleanTuples = false;
        public int carrierSetSize = 2;
        /** Specify the dimensions of the Boolean Tuples used to interpret. */
        public int dimension = 0;
        /** Force the model finder to only return (real) quasi models. */
        public boolean enforceQuasi = false;
        public Engine engine;
        public Engine incrementalEngine;
        public String strategy = "semlab";
    }
}
