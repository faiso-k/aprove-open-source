package aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This processor removes duplicate arguments.
 *
 * <pre>
 * f(x, y, x, z, x) -&gt; ...
 * f(z, 42, 99, null, z) -&gt; ...
 * ... -&gt; f(a, b, a, d, a)
 * results in
 * f(x, y, x, z) -&gt; ...
 * f(z, 42, 99, null) -&gt; ...
 * ... -&gt; f(a, b, a, d)
 * </pre>
 * @author cotto
 */
public class DuplicateArgsRemover extends ITRSProcessor {
    /**
     * The proof for this processor giving information about the duplicate
     * arguments and how they are removed.
     * @author cotto
     */
    private class DuplicateArgsRemoverProof extends ArgumentsRemovalProof {
        /**
         * Create a new proof.
         * @param itrsProblem the ITRSProblem that has been processed
         * @param removedArgs information about removed arguments.
         */
        public DuplicateArgsRemoverProof(
                final ITRSProblem itrsProblem,
                final Collection<Rule> removedArgs) {
            super(itrsProblem, removedArgs);
        }

        /**
         * @return the proof as a nice string representation.
         * @param eu an export util helping with formatting.
         * @param level not used.
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb =
                new StringBuilder(
                    "Some arguments are removed because they only appear as duplicates.");
            sb.append(eu.linebreak());
            super.export(eu, sb);
            return sb.toString();
        }
    }

    private void init(final Set<GeneralizedRule> rules,
            final IDPPredefinedMap predefinedMap,
            final CollectionMap<FunctionSymbol, Collection<Collection<Position>>> fsToPositionPartitions) {
        for (final GeneralizedRule r: rules) {
            for (final TRSTerm foo : r.getTerms()) {
                for (final TRSTerm t : foo.getSubTerms()) {
                    if (t instanceof TRSFunctionApplication) {
                        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                        final FunctionSymbol fs = fa.getRootSymbol();
                        if (!predefinedMap.isPredefined(fs) && !fs.equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL)) {
                            fsToPositionPartitions.add(fs, this.getPositionPartition(fa, predefinedMap));
                        }
                    }
                }
            }
        }
    }

    private Collection<Collection<Position>> getPositionPartition(
            final TRSFunctionApplication fa,
            final IDPPredefinedMap predefinedMap) {
        final CollectionMap<TRSTerm, Position> subtermToPositions =
            new CollectionMap<TRSTerm, Position>();

        /*
         * Go over all positions and fill the map from subterm to position. The
         * resulting value set of the collection map is a partition as we need
         * it.
         */
        for (final Pair<Position, TRSTerm> pos : fa.getPositionsWithSubTerms()) {
            subtermToPositions.add(pos.y, pos.x);
        }

        return subtermToPositions.values();
    }


    /**
     * Yes, we can.
     * @param itrs any itrs
     * @return true
     */
    @Override
    public boolean isITRSApplicable(final ITRSProblem itrs) {
        return true;
    }

    public Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                  Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                  Collection<Rule>> processRulePair(
            final Set<GeneralizedRule> pRules,
            final Set<GeneralizedRule> rRules,
            final IDPPredefinedMap predefinedMap) {
        /*
         * This map stores for each function symbol one collection entry per
         * occurrence in the TRS (on RHS or LHS, we don't care). This entry is
         * a partition (stored as collection of collections) of the positions
         * in the corresponding function application f, where two positions \pi,
         * \tau are equivalent if f|_\pi = f|_\tau.
         */
        final CollectionMap<FunctionSymbol, Collection<Collection<Position>>> fsToPositionPartitions =
            new CollectionMap<FunctionSymbol, Collection<Collection<Position>>>();


        boolean didSomething = false;
        final CollectionMap<FunctionSymbol, Integer> positionsToRemove =
            new CollectionMap<FunctionSymbol, Integer>();

        //Call init twice, once for each rule set:
        this.init(pRules, predefinedMap, fsToPositionPartitions);
        this.init(rRules, predefinedMap, fsToPositionPartitions);

        //Now iterate over all function symbols:
        for (final Entry<FunctionSymbol, Collection<Collection<Collection<Position>>>> e : fsToPositionPartitions.entrySet()) {
            final FunctionSymbol fs = e.getKey();
            final Collection<Collection<Collection<Position>>> positionPartitions = e.getValue();
            /*
             * Now take the first partition. Check for each equivalent pair of
             * positions if they are equivalent in the rest of the partitions.
             * If yes, we have a duplicate!
             */
            final Collection<Collection<Position>> firstPartition =
                positionPartitions.iterator().next();
            for (final Collection<Position> eqClass : firstPartition) {
                int deletedFromThisEqClass = 0;
                int smallestEqClassForThis = eqClass.size();
                //Uninteresting:
                if (eqClass.size() < 2) {
                    continue;
                }
                for (final Position posA : eqClass) {
                    //At least one of the positions should be toplevel. We require this for A:
                    if (posA.getDepth() != 1) {
                        continue;
                    }
                    OTHER_POSITION:
                    for (final Position posB : eqClass) {
                        boolean posBisDuplicate = true;
                        if (posA == posB) {
                            continue;
                        }
                        OTHER_PARTITION:
                        for (final Collection<Collection<Position>> otherPartition : positionPartitions) {
                            if (otherPartition == firstPartition) {
                                continue;
                            }
                            for (final Collection<Position> otherEqClass : otherPartition) {
                                if (otherEqClass.contains(posA)) {
                                    smallestEqClassForThis = Math.min(smallestEqClassForThis, otherEqClass.size());
                                    if (!otherEqClass.contains(posB)) {
                                        //They are not equivalent in this partition. Go to next position.
                                        posBisDuplicate = false;
                                        continue OTHER_POSITION;
                                    } else {
                                        //They are equivalent in this partition. Try next one:
                                        continue OTHER_PARTITION;
                                    }
                                }
                                if (otherEqClass.contains(posB)) {
                                    if (!otherEqClass.contains(posA)) {
                                        //They are not equivalent in this partition. Go to next position.
                                        posBisDuplicate = false;
                                        continue OTHER_POSITION;
                                    } else {
                                        //They are equivalent in this partition. Try next one:
                                        continue OTHER_PARTITION;
                                    }
                                }
                            }
                        }
                        if (posBisDuplicate) {
                            //Mark posA as duplicate.
                            //If there is only one other position in the equivalence
                            //class left, we cannot remove it (as we would then
                            //remove all copies). Thus, stop here.
                            if (smallestEqClassForThis - deletedFromThisEqClass > 1) {
                                deletedFromThisEqClass++;
                                positionsToRemove.add(fs, (posA.toIntArray())[0]);
                                didSomething = true;
                                break;
                            }
                        }
                    }
                }
            }
        }

        if (!didSomething) {
            // No argument can be removed
            return null;
        }

        // Construct the result
        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newRPair =
            HelperClass.getResultingRules(rRules, predefinedMap, positionsToRemove, new LinkedHashSet<FunctionSymbol>());

        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newPPair =
            HelperClass.getResultingRules(pRules, predefinedMap, positionsToRemove, new LinkedHashSet<FunctionSymbol>());

        return new Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                          Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                          Collection<Rule>>(newPPair, newRPair, ArgumentsRemovalProof.getFilterRules(positionsToRemove, newPPair.y));
    }

    /**
     * Start working on the given ITRS.
     * @param itrs some itrs
     * @param aborter an aborter
     * @return the ITRS with duplicates removed (together with a proof and such)
     * @throws AbortionException never.
     */
    @Override
    protected Result processITRSProblem(final ITRSProblem itrs, final Abortion aborter)
            throws AbortionException {
        final Triple<Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                     Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>>,
                     Collection<Rule>>
             resultTriple =
                 this.processRulePair(Collections.EMPTY_SET, itrs.getR(), itrs.getPredefinedMap());

        if (resultTriple == null) {
            // No argument can be removed
            return ResultFactory.unsuccessful();
        }

        final Pair<Set<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> newRulesPair = resultTriple.y;
        final Set<GeneralizedRule> newRules = newRulesPair.x;
        final Collection<Rule> positionsToBeRemoved = resultTriple.z;


        final IQTermSet newQ = new IQTermSet(HelperClass.getNewQ(newRules), itrs.getPredefinedMap());
        final ITRSProblem newItrs = ITRSProblem.create(newRules, newQ);

        final DuplicateArgsRemoverProof proof =
            new DuplicateArgsRemoverProof(newItrs, positionsToBeRemoved);
        return ResultFactory.proved(newItrs, YNMImplication.EQUIVALENT, proof);
    }

}
