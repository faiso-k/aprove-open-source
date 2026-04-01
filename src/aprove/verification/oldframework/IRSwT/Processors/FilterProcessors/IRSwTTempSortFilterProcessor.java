package aprove.verification.oldframework.IRSwT.Processors.FilterProcessors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.IRSwT.Digraph.*;
import aprove.verification.oldframework.IRSwT.Filters.*;
import aprove.verification.oldframework.IRSwT.Sorts.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Filters temporarily!
 * 1. Remove some stuff
 * 2. Execute the given strategy
 * 3. Return result in form of an IRSwTProblem
 *
 * Please note that the given strategy is required to return a subset of its input problem.
 * Otherwise this processor will fail.
 *
 * @author Matthias Hoelzel
 */
public abstract class IRSwTTempSortFilterProcessor extends IRSwTAbstractSortFilterProcessor {
    /** Arguments that can be passed to this processor. */
    public static class Arguments {
        /** Strategy to execute. */
        UserStrategy strategy;

        /** Time to live! */
        int time = 42042;

        /**
         * Ensures that every variable from the right side also occurs at the left side.
         */
        boolean filterFreeVariables;
    }

    /** Arguments. */
    private final Arguments args;

    public void setStrategy(final String strategyName) {
        this.args.strategy = new VariableStrategy(strategyName);
    }

    public void setTime(final int timeVal) {
        this.args.time = timeVal;
    }

    /**
     * Setter for argument filterFreeVariables
     * @param value boolean
     */
    @Override
    public void setFilterFreeVariables(final boolean value) {
        this.args.filterFreeVariables = value;
    }


    /** Constructor! */
    public IRSwTTempSortFilterProcessor() {
        this.args = new Arguments();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation!";
        final IRSwTProblem irswt = (IRSwTProblem) obl;

        // 1. Deduce the sorts
        final SortAnalyzer sortAnalyzer = new SortAnalyzer(irswt.getRules());
        final SortDictionary sorts = sortAnalyzer.analyze();

        // 2. Apply filter:
        final AbstractFilter filter = this.createFilter(irswt, sorts);
        final LinkedHashSet<IGeneralizedRule> filteredRules = filter.applyFilter();


        final LinkedHashSet<IGeneralizedRule> newRules;
        final AbstractFilter freeVarFilter;
        if (this.args.filterFreeVariables) {
            freeVarFilter = new FreeVarFilter(filteredRules);
            newRules = freeVarFilter.applyFilter();
        } else {
            freeVarFilter = null;
            newRules = filteredRules;
        }

        final IRSwTProblem newProblem;
        if (filter instanceof RemoveTermFilter || filter instanceof RetainIntFilter) {
            newProblem = new IRSProblem(ImmutableCreator.create(newRules), irswt.getStartTerm());
        } else {
            newProblem = new IRSwTProblem(ImmutableCreator.create(newRules), irswt.getStartTerm());
        }

        final BasicObligationNode newOblNode = new BasicObligationNode(newProblem);

        final Abortion childAbortion = aborter.createChild(this.args.time);
        final StrategyExecutionHandle handle =
            Machine.theMachine.startSubMachine(
                this.args.strategy,
                rti.getProgram(),
                newOblNode,
                null,
                childAbortion.getClocks(),
                false
            );

        try {
            handle.waitForFinish();
        } catch (final InterruptedException e) {
            throw new AbortionException("TempSortFilter interrupted: " + e.getMessage());
        }

        if (handle.isFinished()) {
            final ExecutableStrategy execStrat = handle.getResult();

            if (execStrat != null && !execStrat.isFail() && execStrat instanceof Success) {
                final Success s = (Success) execStrat;
                final ImmutableList<BasicObligationNode> positions = s.getPositions();

                if (positions.isEmpty() && !newOblNode.getTruthValue().equals(YNM.YES)) {
                    return ResultFactory.unsuccessful("Could not remove any rules!");
                }

                final LinkedHashSet<IGeneralizedRule> bonRules = new LinkedHashSet<>();
                for (final BasicObligationNode bon : positions) {
                    bonRules.addAll(this.translateBon(bon));
                }

                final LinkedHashSet<IGeneralizedRule> resultingOriginalRules;
                if (freeVarFilter != null) {
                    final LinkedHashSet<IGeneralizedRule> resultingTempRules = freeVarFilter.getOldRules(bonRules);
                    if (resultingTempRules == null) {
                        assert false : "Rules have been changed!";
                        return ResultFactory.unsuccessful();
                    }
                    resultingOriginalRules = filter.getOldRules(resultingTempRules);
                } else {
                    resultingOriginalRules = filter.getOldRules(bonRules);
                }

                if (resultingOriginalRules == null) {
                    assert false : "Rules have been changed!";
                    return ResultFactory.unsuccessful();
                }

                if (resultingOriginalRules.containsAll(irswt.getRules())) {
                    return ResultFactory.unsuccessful("Could not simplify filtered rules!");
                } else {
                    final PartiallyComputedDigraph<IGeneralizedRule> digraph = irswt.getTerminationDigraph();
                    final PartiallyComputedDigraph<IGeneralizedRule> newDigraph =
                        digraph == null ? null : digraph.getInducedSubgraph(resultingOriginalRules);

                    final IRSwTProblem result =
                        new IRSwTProblem(ImmutableCreator.create(resultingOriginalRules), newDigraph);
                    final BasicObligationNode resultNode = new BasicObligationNode(result);

                    boolean done = resultingOriginalRules.isEmpty();
                    if (newDigraph != null) {
                        newDigraph.overestimate();
                        if (Options.certifier.isNone()) {
                            done = newDigraph.hasOnlyTrivialSCCs();
                        }
                    }
                    TempFilterProof proof = new TempFilterProof(filter, sorts, newOblNode, done, irswt);

                    if (done) {
                        newOblNode.recursiveRepropagateTruthValues();
                        final ExecutableStrategy succStrategy = Success.EMPTY;
                        return ResultFactory.provedWithNewStrategy(
                            newOblNode,
                            YNMImplication.SOUND,
                            proof,
                            succStrategy);
                    } else {
                        // TODO: currently CeTA is not capable of checking partial proofs
                        if (Options.certifier.isNone()) {
                            return ResultFactory.proved(result, YNMImplication.SOUND, proof);
                        } else {
                            return ResultFactory.unsuccessful("Partial proof for IRSwT not certifiable");
                        }
                    }
                }
            }
        } else {
            aborter.checkAbortion();
        }

        return ResultFactory.unsuccessful();
    }

    public Set<IGeneralizedRule> translateBon(final BasicObligationNode bon) {
        final BasicObligation bo = bon.getBasicObligation();
        if (bo instanceof IRSwTProblem) {
            return ((IRSwTProblem) bo).getRules();
        } else if (bo instanceof QDPProblem) {
            final Set<Rule> rules = ((QDPProblem) bo).getP();
            final LinkedHashSet<IGeneralizedRule> result = new LinkedHashSet<>();
            for (final Rule r : rules) {
                // Now we "igeneralize" the rule:
                final TRSFunctionApplication left = r.getLeft();
                final TRSTerm right = r.getRight();
                final IGeneralizedRule iRule = IGeneralizedRule.create(left, right, null);
                result.add(iRule);
            }
            return result;
        } else {
            assert false : "Unknown obligation!";
            return null;
        }
    }

    /**
     * A truly flimflammed proof!
     * @author Matthias Hoelzel
     */
    class TempFilterProof extends DefaultProof {
        // TODO: Somehow include proof of executed strategy!!
        /** Stores the filter we applied. */
        private final AbstractFilter filter;

        /** Some sort dictionary. */
        private final SortDictionary sortDict;

        /** Obligation node where substrategy has been applied. */
        private final BasicObligationNode subBon;
        
        private final boolean done;
        
        private final IRSLike origProb;

        /**
         * Constructor!
         * @param abstractFilter the applied filter
         * @param sortDictionary some sort dictionary
         */
        public TempFilterProof(final AbstractFilter abstractFilter, final SortDictionary sortDictionary,
                final BasicObligationNode bon, final boolean done, IRSLike origProb) {
            this.filter = abstractFilter;
            this.sortDict = sortDictionary;
            this.subBon = bon;
            this.done = done;
            this.origProb = origProb;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append(eu.tttext("Used the following sort dictionary for filtering: "));
            sb.append(this.sortDict.export(eu));
            sb.append(eu.linebreak());
            sb.append(this.filter.export(eu));

            if (!done) {
                sb.append("The following proof was generated: ");
                final GenericExportManager subproof =
                        new GenericExportManager(TempFilterProof.this.subBon, "filtering result", false);
                sb.append(eu.preFormatted(subproof.export(new PLAIN_Util())));
            }

            return sb.toString();
        }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            return childrenProofs[0];
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
        }
        
        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData xmlPreMetaData) {
            Map<IGeneralizedRule,IGeneralizedRule> oldNew = new HashMap<>();
            for (IGeneralizedRule rule : this.origProb.getRules()) {
                oldNew.put(rule, this.filter.getNewRule(rule));
            }
            return xmlPreMetaData.adjustOldNew(oldNew).integrateFilter(this.filter);
        }


    }
}
