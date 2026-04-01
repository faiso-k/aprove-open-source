package aprove.verification.dpframework.TRSProblem.Processors.FromITRS;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

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
public class DuplicateArgsRemover extends QTRSProcessor {
    /**
     * The proof for this processor giving information about the duplicate
     * arguments and how they are removed.
     * @author cotto
     */
    private class DuplicateArgsRemoverProof extends ArgumentsRemovalProof {
        /**
         * Create a new proof.
         * @param removedArgs information about removed arguments.
         * @param names information about name changes.
         */
        public DuplicateArgsRemoverProof(
                final CollectionMap<FunctionSymbol, Integer> removedArgs,
                final Map<FunctionSymbol, FunctionSymbol> names) {
            super(removedArgs, names);
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

    /**
     * Yes, we can.
     * @param qtrs any qtrs
     * @return true
     */
    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return true;
    }

    /**
     * Start working on the given QTRS.
     * @param qtrs some qtrs
     * @param aborter an aborter
     * @return the QTRS with duplicates removed (together with a proof and such)
     * @param rti don't know
     * @throws AbortionException never.
     */
    @Override
    protected Result processQTRS(final QTRSProblem qtrs,
        final Abortion aborter,
        final RuntimeInformation rti)
            throws AbortionException {
        final ImmutableSet<Rule> rules = qtrs.getR();

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

        //Init our partition
        this.init(rules, fsToPositionPartitions);

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
            return ResultFactory.unsuccessful();
        }

        // Construct the result
        final Pair<QTRSProblem, Map<FunctionSymbol, FunctionSymbol>> pair =
            HelperClass.getResultingQTRS(qtrs, positionsToRemove);
        final DuplicateArgsRemoverProof proof =
            new DuplicateArgsRemoverProof(positionsToRemove, pair.y);
        return ResultFactory.proved(pair.x, YNMImplication.EQUIVALENT, proof);
    }

    private void init(final ImmutableSet<Rule> rules,
            final CollectionMap<FunctionSymbol, Collection<Collection<Position>>> fsToPositionPartitions) {
        for (final Rule r : rules) {
            for (final TRSTerm foo : r.getTerms()) {
                for (final TRSTerm t : foo.getSubTerms()) {
                    if (t instanceof TRSFunctionApplication) {
                        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                        final FunctionSymbol fs = fa.getRootSymbol();
                        fsToPositionPartitions.add(fs, this.getPositionPartition(fa));
                    }
                }
            }
        }
    }

    private Collection<Collection<Position>> getPositionPartition(
            final TRSFunctionApplication fa) {
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
}
