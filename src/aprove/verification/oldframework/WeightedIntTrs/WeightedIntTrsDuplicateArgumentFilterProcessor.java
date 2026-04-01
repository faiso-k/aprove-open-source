package aprove.verification.oldframework.WeightedIntTrs;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
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
 * @author cotto, Marc Brockschmidt
 */
public class WeightedIntTrsDuplicateArgumentFilterProcessor extends WeightedIntTrsArgumentFilter {

    @ParamsViaArgumentObject
    public WeightedIntTrsDuplicateArgumentFilterProcessor(Arguments args) {
        super(args);
    }

    /**
     * Create initial map of function symbols to a partition of their arguments (where positions are in the same eq
     *  class if they always contain the same term)
     * @param rules the rules to look at
     * @param fsToPositionPartitions the
     */
    private static <T extends AbstractWeightedIntRule<T>>  void init(
        final Set<T> rules,
        final CollectionMap<FunctionSymbol, Collection<Collection<Position>>> fsToPositionPartitions)
    {
        final IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        for (final T r : rules) {
            for (final TRSFunctionApplication foo : r.getTerms()) {
                for (final TRSTerm t : foo.getSubTerms()) {
                    if (t instanceof TRSFunctionApplication) {
                        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
                        final FunctionSymbol fs = fa.getRootSymbol();
                        if (!predefinedMap.isPredefined(fs) && !fs.equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL))
                        {
                            fsToPositionPartitions.add(fs, getPositionPartition(fa));
                        }
                    }
                }
            }
        }
    }

    /**
     * @param fa some function application
     * @return a partition of the arguments (where the positions are in the same eq class if they contain the same term)
     */
    private static Collection<Collection<Position>> getPositionPartition(final TRSFunctionApplication fa) {
        final CollectionMap<TRSTerm, Position> subtermToPositions = new CollectionMap<>();
        for (final Pair<Position, TRSTerm> pos : fa.getPositionsWithSubTerms()) {
            subtermToPositions.add(pos.y, pos.x);
        }

        return subtermToPositions.values();
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        return processInternal((AbstractWeightedIntTermSystem<?>) obl);
    }

    private <T extends AbstractWeightedIntRule<T>> Result processInternal(AbstractWeightedIntTermSystem<T> obl) throws AbortionException {
        final Pair<Pair<Set<T>, Map<FunctionSymbol, FunctionSymbol>>, CollectionMap<FunctionSymbol, Integer>> r =
            processRules(obl.getRules());

        if (r != null) {
            final TRSFunctionApplication newStartTerm;
            if (obl.getStartTerm() != null) {
                newStartTerm =
                    (TRSFunctionApplication) HelperClass.remove(
                        obl.getStartTerm(),
                        r.y,
                        r.x.y,
                        r.y.keySet(),
                        IDPPredefinedMap.DEFAULT_MAP);
            } else {
                newStartTerm = null;
            }

            if (this.args.propagateLowerBounds()) {
                return ResultFactory.proved(
                        obl.copyWithNewRules(r.x.x, newStartTerm),
                        SoundUpperUnsoundLowerBound.forConcreteBounds(),
                        new WeightedIntTrsDuplicateArgumentFilterProof(ArgumentsRemovalProof.getFilterRules(r.y, r.x.y)));
            } else {
                return ResultFactory.proved(
                        obl.copyWithNewRules(r.x.x, newStartTerm),
                        UpperBound.forConcreteBounds(),
                        new WeightedIntTrsDuplicateArgumentFilterProof(ArgumentsRemovalProof.getFilterRules(r.y, r.x.y)));
            }
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    /**
     * @param rules some set of rules
     * @return a pair of filtered rules and a mapping detailing which positions are to be filtered
     */
    public static <T extends AbstractWeightedIntRule<T>> WeightedArgumentFilterResult<T> processRules(final Set<T> rules) {
        return processRules(rules, Collections.emptySet());
    }

    /**
     * @param rules some set of rules
     * @param protectedSymbols TODO document me
     * @return a pair of filtered rules and a mapping detailing which positions are to be filtered
     */
    public static <T extends AbstractWeightedIntRule<T>>  WeightedArgumentFilterResult<T> processRules(
        Set<T> rules,
        Set<FunctionSymbol> protectedSymbols
    ) {
        /*
         * This map stores for each function symbol one collection entry per
         * occurrence in the TRS (on RHS or LHS, we don't care). This entry is
         * a partition (stored as collection of collections) of the positions
         * in the corresponding function application f, where two positions \pi,
         * \tau are equivalent if f|_\pi = f|_\tau.
         */
        final CollectionMap<FunctionSymbol, Collection<Collection<Position>>> fsToPositionPartitions =
            new CollectionMap<>();

        //Call init, finding out where positions are duplicated:
        init(rules, fsToPositionPartitions);

        boolean didSomething = false;
        final CollectionMap<FunctionSymbol, Integer> positionsToRemove = new CollectionMap<>();
        //Now iterate over all function symbols:
        for (final Entry<FunctionSymbol, Collection<Collection<Collection<Position>>>> e : fsToPositionPartitions
            .entrySet())
        {
            final FunctionSymbol fs = e.getKey();
            final Collection<Collection<Collection<Position>>> positionPartitions = e.getValue();
            /*
             * Now take the first partition. Check for each equivalent pair of
             * positions if they are equivalent in the rest of the partitions.
             * If yes, we have a duplicate!
             */
            final Collection<Collection<Position>> firstPartition = positionPartitions.iterator().next();
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
                    OTHER_POSITION: for (final Position posB : eqClass) {
                        boolean posBisDuplicate = true;
                        if (posA == posB) {
                            continue;
                        }
                        OTHER_PARTITION: for (final Collection<Collection<Position>> otherPartition : positionPartitions)
                        {
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
                        if (posBisDuplicate && posA.getDepth() == 1 && posB.getDepth() == 1) {
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

        //Do not filter in certain symbols:
        for (final FunctionSymbol protectedSym : protectedSymbols) {
            positionsToRemove.remove(protectedSym);
        }

        if (!didSomething) {
            // No argument can be removed
            return null;
        }

        // Construct the result
        final Pair<Set<T>, Map<FunctionSymbol, FunctionSymbol>> newRulePair =
            getResultingRules(rules, positionsToRemove, new LinkedHashSet<FunctionSymbol>());

        return new WeightedArgumentFilterResult<>(newRulePair, positionsToRemove);
    }

    /**
     * The proof for this processor giving information about the removed positions.
     * @author Jera Hensel
     */
    private static class WeightedIntTrsDuplicateArgumentFilterProof extends DefaultProof {
        /**
         * The arguments that are removed.
         */
        private final Collection<Rule> rem;

        /**
         * Create a new proof.
         * @param removedArgs maps function symbols to the list of removed argument positions
         */
        public WeightedIntTrsDuplicateArgumentFilterProof(final Collection<Rule> removedArgs) {
            this.rem = removedArgs;
        }

        /**
         * @return the proof as a nice string representation.
         * @param o an export util helping with formatting.
         * @param level not used.
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("Some arguments are removed because they are duplicates. ");
            sb.append("We removed arguments according to the following replacements:");
            sb.append(o.linebreak());
            sb.append(o.set(this.rem, Export_Util.RULES));
            return sb.toString();
        }
    }
}
