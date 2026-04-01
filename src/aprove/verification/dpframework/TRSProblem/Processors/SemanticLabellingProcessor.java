package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Rewriting.SemanticLabelling.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Semantic Labelling Processor
 *
 * @author thiemann
 */

public class SemanticLabellingProcessor extends Processor.ProcessorSkeleton {

    private final static Logger log = Logger.getLogger("semlab Logger");

    /**
     * An <code>int</code> containing the size of the carrier set of possible models.
     */
    private final int carrierSetSize;
    private final boolean allowQuasi;
    private final UserStrategy strategy;

    private final Engine engine;

    @ParamsViaArgumentObject
    public SemanticLabellingProcessor(final Arguments arguments) {
        this.carrierSetSize = arguments.carrierSetSize;
        this.allowQuasi = arguments.allowQuasi;
        this.engine = arguments.engine;
        this.strategy = this.parseRange(arguments.range);
    }

    public UserStrategy parseRange(final int range) {
        return StrategyTranslator.strategyFragment("RepeatS(1,*,QTRSRRR[Order = POLO[Degree = 1, Range = "
            + range
            + ", Autostrict = False, MaxSimpleDegree = 5, Engine = MINISAT]])");
    }

    @Override
    public boolean isApplicable(final BasicObligation o) {
        return (o instanceof QTRSProblem) && !((QTRSProblem) o).getR().isEmpty();
    }

    private static final Set<FunctionSymbol> EMPTY_SET = new LinkedHashSet<FunctionSymbol>();

    @Override
    public Result process(
        final BasicObligation bobl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        final QTRSProblem qtrs = (QTRSProblem) bobl;
        final Set<Rule> rules = qtrs.getR();
        final int Rsize = rules.size();
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap =
            new LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>>();

        // Let's find all possible Models for the current TRS, do not regard Q, as we only use RRR.

        // RT: Note that C. Hangs PolyomialFunctionRepresentation will only generate polys with interpretations
        // that can be expressed with CarrierSetSize 2. So do not wonder, that constant 2 or something like that
        // is not generated if you choose CarrierSetSize 3.
        final Iterator<Pair<Boolean, Labeller>> iter =
            Model.getModelIterator(rules, qtrs.getRSignature(), SemanticLabellingProcessor.EMPTY_SET, new PolynomialFunctionRepresentation(
                this.carrierSetSize), this.allowQuasi, false, null);
        Set<Rule> decrRules = null;

        int dropped = 0;
        int count = 0;

        while (iter.hasNext()) {
            count++;

            final Pair<Boolean, Labeller> o = iter.next();
            final Labeller l = o.y;

            // build labelled rules
            int newRsize = 0;
            final Collection<Pair<Rule, Collection<Rule>>> labelledR =
                new ArrayList<Pair<Rule, Collection<Rule>>>(rules.size());
            for (final Rule rule : rules) {
                final Collection<Rule> labelledRules = new ArrayList<Rule>();
                l.addLabeled(rule, labelledRules, xmlLabelMap);
                newRsize += labelledRules.size();
                labelledR.add(new Pair<Rule, Collection<Rule>>(rule, labelledRules));
            }

            // check effective labelling
            if (Labeller.EffectiveChecker.checkIneffective(labelledR, l, this.engine, aborter)) {
                dropped++;
                continue;
            }

            // build newR and newP
            final Set<Rule> newRules = new LinkedHashSet<Rule>(newRsize);
            for (final Pair<Rule, Collection<Rule>> labelledRules : labelledR) {
                newRules.addAll(labelledRules.y);
            }

            final boolean quasi = o.x;
            SemanticLabellingProcessor.log.log(Level.FINE, "Checking " + (quasi ? "quasi-" : "") + "model: {0}\n", l);

            if (quasi) {
                // only compute decr rules once, as they only depend on the signature and the carrierSetSize
                if (decrRules == null) {
                    decrRules = l.getDecreasingRules(xmlLabelMap);
                }
                newRules.addAll(decrRules);
            }

            // we do not create labeled Q here, as it is not needed for RRR-processor!
            final QTRSProblem labelledTRS = QTRSProblem.create(ImmutableCreator.create(newRules));

            final BasicObligationNode labelledTRSNode = new BasicObligationNode(labelledTRS);
            final StrategyExecutionHandle handle =
                Machine.theMachine.startSubMachine(
                    this.strategy,
                    null,
                    labelledTRSNode,
                    null,
                    aborter.getClocks(),
                    false);

            HandleChecker.check(handle, aborter);

            // okay, we have the result after the RRR processor
            final ExecutableStrategy result = handle.getResult();
            if (result.isFail()) {
                continue; // we have not performed one RRR step, so unlabelling will result in the original TRS.
            } else {
                Set<Rule> finalRules;
                final List<BasicObligationNode> newProblems = ((Success) result).getPositions();
                if (newProblems.isEmpty()) {
                    // hooray, we have proven it completely.
                    finalRules = null;
                } else {
                    if (newProblems.size() > 1) { // RRR cannot produce more than one result!
                        throw new RuntimeException("Bug in Semlab");
                    }
                    final QTRSProblem labelledTRSAfterRRR = (QTRSProblem) newProblems.get(0).getBasicObligation();

                    // compute the original rules that remain after unlabelling
                    finalRules = new LinkedHashSet<Rule>(Rsize);
                    for (final Rule rule : labelledTRSAfterRRR.getR()) {
                        if (!newRules.contains(rule)) {
                            if (Globals.useAssertions) {
                                assert (false) : "semlab used with rule modyfying processor";
                            } else {
                                return ResultFactory.unsuccessful("semlab was invoked with a strategy changing rules!");
                            }
                        }
                        finalRules.add(l.unlabel(rule));
                    }

                    // to get rid of unlabelled decr rules
                    if (quasi) {
                        finalRules.retainAll(rules);
                    }
                    if (Globals.useAssertions) {
                        assert (rules.containsAll(finalRules));
                    }
                    if (finalRules.size() == Rsize) {
                        continue; // we have gained nothing
                    }
                }

                // okay, we have successfully applied semlab.
                // now build final result
                SemanticLabellingProcessor.log.log(Level.INFO, "\n\nDropped " + dropped + " of " + count + " models by effective labelling\n\n\n");

                final boolean solvedCompletely = finalRules == null;
                final Proof proof = new SemLabProof(labelledTRS, quasi, l, xmlLabelMap, qtrs, solvedCompletely);
                if (solvedCompletely) {
                    final ExecutableStrategy succStrategy = Success.EMPTY;
                    return ResultFactory.provedWithNewStrategy(
                        labelledTRSNode,
                        YNMImplication.SOUND,
                        proof,
                        succStrategy);
                } else {
                    final QTRSProblem finalQTRS = qtrs.createSubProblem(ImmutableCreator.create(finalRules));
                    final QTRSProblem qtrsCopy = qtrs.createSubProblem(qtrs.getR()); // create a copy of qdp with a possibly different truth value
                    final BasicObligationNode relativeNode = new BasicObligationNode(qtrsCopy);
                    final ObligationNodeChild relativeChild =
                        new ObligationNodeChild(labelledTRSNode, proof, YNMImplication.SOUND);
                    relativeNode.addTechnique(relativeChild, false);
                    final Processor proc = new QTRSSplitProcessor(relativeNode, newProblems, finalQTRS);
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
     * Proof which prints out the resulting QTRSProblem
     */
    private class SemLabProof extends QTRSProof {

        QTRSProblem labelledTRS;
        boolean quasi;
        Labeller labeller;
        private final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap;
        private final QTRSProblem origObl;
        private final boolean requireOnlineCertification;

        private SemLabProof(
            final QTRSProblem labelledTRS,
            final boolean quasi,
            final Labeller labeller,
            final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap,
            final QTRSProblem origObl,
            final boolean requireOnlineCertification)
        {
            this.labelledTRS = labelledTRS;
            this.quasi = quasi;
            this.labeller = labeller;
            this.xmlLabelMap = xmlLabelMap;
            this.origObl = origObl;
            this.requireOnlineCertification = requireOnlineCertification;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append("We found the following " + (this.quasi ? "quasi-" : "") + "model for the rules of the TRS.\n");
            s.append(this.labeller.export(eu));
            s.append("By semantic labelling "
                + eu.cite(Citation.SEMLAB)
                + " and forgetting Q we result in the following labelled TRS.");
            return s.toString();
        }

        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData preData) {
            return new XMLMetaData(this.xmlLabelMap, preData);
        }

        @Override
        public boolean requireFullSubproof(final CPFModus modus, final int i) {
            return this.requireOnlineCertification;
        }

    }

    public static class Arguments {
        public boolean allowQuasi = true;
        public int carrierSetSize = 2;
        public Engine engine;
        public int range = 2;
    }
}
