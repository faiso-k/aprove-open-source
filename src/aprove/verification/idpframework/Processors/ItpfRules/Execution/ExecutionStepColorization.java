package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.awt.*;
import java.util.*;
import java.util.Map.Entry;
import java.util.List;

import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class ExecutionStepColorization {

    public static final ExecutionStepColorization EMPTY = ExecutionStepColorization.create(Collections.<Pair<? extends ExecutionMarkable, ? extends ExecutionMarkable>> emptyList());
    private static final int MAIN_COLOR_ADD = 192;
    private static final int MAX_COLOR_BRIGHTNESS = 255;

    public static ExecutionStepColorization create(final List<? extends Pair<? extends ExecutionMarkable, ? extends ExecutionMarkable>> steps) {
        final Map<ExecutionMarkable, Set<ExecutionMarkable>> equivalenceClasses =
            new LinkedHashMap<ExecutionMarkable, Set<ExecutionMarkable>>();

        for (final Pair<? extends ExecutionMarkable, ? extends ExecutionMarkable> step : steps) {
            final ExecutionMarkable source = step.x;
            final ExecutionMarkable target = step.y;

            final Map<ExecutionUid, ExecutionMarkable> sourceExecutionMarks = new LinkedHashMap<ExecutionUid, ExecutionMarkable>();
            source.collectExecutionMarks(sourceExecutionMarks);

            final Map<ExecutionUid, ExecutionMarkable> targetExecutionMarks = new LinkedHashMap<ExecutionUid, ExecutionMarkable>();
            target.collectExecutionMarks(targetExecutionMarks);

            ExecutionStepColorization.cleanupExecutionMarks(sourceExecutionMarks, targetExecutionMarks);

            // add new classes
            for (final Entry<ExecutionUid, ExecutionMarkable> sourceExecEntry : sourceExecutionMarks.entrySet()) {
                final ExecutionMarkable execSource = sourceExecEntry.getValue();
                final ExecutionMarkable execTarget = targetExecutionMarks.get(sourceExecEntry.getKey());
                if (execTarget != null) {
                    ExecutionStepColorization.makeEqeuivalent(execSource, execTarget, equivalenceClasses);
                } else {
                    ExecutionStepColorization.makeEqeuivalent(execSource, execSource, equivalenceClasses);
                }
            }
        }

        final ImmutableMap<ExecutionMarkable, ImmutableSet<ExecutionMarkable>> immutableEquivalenceClasses =
            ImmutableCreator.create(CollectionUtil.immutableSetMap(equivalenceClasses));

        final Map<ImmutableSet<ExecutionMarkable>, Integer> colors = ExecutionStepColorization.createColors(immutableEquivalenceClasses.values());

        return new ExecutionStepColorization(immutableEquivalenceClasses, ImmutableCreator.create(colors));
    }

    private static Map<ImmutableSet<ExecutionMarkable>, Integer> createColors(final Collection<ImmutableSet<ExecutionMarkable>> immutableEquivalenceClasses) {


        final int[][] mainColorAdd = new int[][]{
            new int[]{ExecutionStepColorization.MAIN_COLOR_ADD, 0, 0},
            new int[]{-ExecutionStepColorization.MAIN_COLOR_ADD, ExecutionStepColorization.MAIN_COLOR_ADD, 0},
            new int[]{0, -ExecutionStepColorization.MAIN_COLOR_ADD, ExecutionStepColorization.MAIN_COLOR_ADD},
            new int[]{ExecutionStepColorization.MAIN_COLOR_ADD, ExecutionStepColorization.MAIN_COLOR_ADD, -ExecutionStepColorization.MAIN_COLOR_ADD},
            new int[]{0, -ExecutionStepColorization.MAIN_COLOR_ADD, ExecutionStepColorization.MAIN_COLOR_ADD},
            new int[]{-ExecutionStepColorization.MAIN_COLOR_ADD, ExecutionStepColorization.MAIN_COLOR_ADD, 0},
            new int[]{0, -ExecutionStepColorization.MAIN_COLOR_ADD, -ExecutionStepColorization.MAIN_COLOR_ADD},
        };
        final int[][] shiftColorAdd = new int[][]{new int[]{0, 0, 40}, new int[]{0, 30, 0}, {50, 0, 0}};

        final Map<ImmutableSet<ExecutionMarkable>, Integer> res = new LinkedHashMap<ImmutableSet<ExecutionMarkable>, Integer>();

        int r = 0;
        int g = 0;
        int b = 0;

        int mainColorAddIndex = 0;
        int shiftColorAddIndex = 0;

        for (final ImmutableSet<ExecutionMarkable> eqClass : immutableEquivalenceClasses) {
            do {
                r = (r + mainColorAdd[mainColorAddIndex][0] + ExecutionStepColorization.MAX_COLOR_BRIGHTNESS) % ExecutionStepColorization.MAX_COLOR_BRIGHTNESS;
                g = (g + mainColorAdd[mainColorAddIndex][1] + ExecutionStepColorization.MAX_COLOR_BRIGHTNESS) % ExecutionStepColorization.MAX_COLOR_BRIGHTNESS;
                b = (b + mainColorAdd[mainColorAddIndex][2] + ExecutionStepColorization.MAX_COLOR_BRIGHTNESS) % ExecutionStepColorization.MAX_COLOR_BRIGHTNESS;

                if (mainColorAddIndex == mainColorAdd.length - 1) {
                    mainColorAddIndex = 0;
                    r = (r + shiftColorAdd[shiftColorAddIndex][0] + ExecutionStepColorization.MAX_COLOR_BRIGHTNESS) % ExecutionStepColorization.MAX_COLOR_BRIGHTNESS;
                    g = (g + shiftColorAdd[shiftColorAddIndex][1] + ExecutionStepColorization.MAX_COLOR_BRIGHTNESS) % ExecutionStepColorization.MAX_COLOR_BRIGHTNESS;
                    b = (b + shiftColorAdd[shiftColorAddIndex][2] + ExecutionStepColorization.MAX_COLOR_BRIGHTNESS) % ExecutionStepColorization.MAX_COLOR_BRIGHTNESS;
                    shiftColorAddIndex = (shiftColorAddIndex + 1) % shiftColorAdd.length;
                } else {
                    mainColorAddIndex++;
                }
            } while (r == 0 && g == 0 && b == 0);

            final Color color = new Color(r, g, b, 0);
            res.put(eqClass, color.getRGB());
        }

        return res ;
    }

    private static void makeEqeuivalent(final ExecutionMarkable execSource,
        final ExecutionMarkable execTarget,
        final Map<ExecutionMarkable, Set<ExecutionMarkable>> equivalenceClasses) {

        final Set<ExecutionMarkable> sourceEqClass = equivalenceClasses.get(execSource);
        if (execSource == execTarget) {
            if (sourceEqClass == null) {
                final LinkedHashSet<ExecutionMarkable> newEqClass = new LinkedHashSet<ExecutionMarkable>();
                newEqClass.add(execTarget);
                equivalenceClasses.put(execSource, newEqClass);
            }
        } else {
            final Set<ExecutionMarkable> targetEqClass = equivalenceClasses.get(execTarget);

            if (sourceEqClass != null) {
                if (targetEqClass != null) {
                    // merge classes
                    for (final ExecutionMarkable targetEntry : targetEqClass) {
                        sourceEqClass.add(targetEntry);
                        equivalenceClasses.put(targetEntry, sourceEqClass);
                    }
                } else {
                    sourceEqClass.add(execTarget);
                    equivalenceClasses.put(execTarget, sourceEqClass);
                }
            } else if (targetEqClass != null) {
                targetEqClass.add(execSource);
                equivalenceClasses.put(execSource, targetEqClass);
            } else {
                final LinkedHashSet<ExecutionMarkable> newEqClass = new LinkedHashSet<ExecutionMarkable>();
                newEqClass.add(execSource);
                newEqClass.add(execTarget);

                equivalenceClasses.put(execSource, newEqClass);
                equivalenceClasses.put(execTarget, newEqClass);
            }
        }
    }

    private static Set<ExecutionUid> cleanupExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> sourceExecutionMarks,
        final Map<ExecutionUid, ExecutionMarkable> targetExecutionMarks) {
        final Set<ExecutionUid> unchangedUids = new LinkedHashSet<ExecutionUid>();

        final Iterator<Entry<ExecutionUid, ExecutionMarkable>> sourceIterator =
            sourceExecutionMarks.entrySet().iterator();

        while(sourceIterator.hasNext()) {
            final Entry<ExecutionUid, ExecutionMarkable> sourceEntry = sourceIterator.next();
            final ExecutionMarkable targetValue = targetExecutionMarks.get(sourceEntry.getKey());
            if (targetValue == null) {
                if (!sourceEntry.getKey().isDeletion()) {
                    sourceIterator.remove();
                }
            } else if (sourceEntry.getValue().equals(targetValue)) {
                unchangedUids.add(sourceEntry.getKey());
                targetExecutionMarks.remove(sourceEntry.getKey());
                sourceIterator.remove();
            }
        }

        targetExecutionMarks.keySet().retainAll(sourceExecutionMarks.keySet());

        return unchangedUids;
    }

    private final ImmutableMap<ExecutionMarkable, ImmutableSet<ExecutionMarkable>> equivalenceClasses;
    private final ImmutableMap<ImmutableSet<ExecutionMarkable>, Integer> colors;

    private ExecutionStepColorization(final ImmutableMap<ExecutionMarkable, ImmutableSet<ExecutionMarkable>> equivalenceClasses, final ImmutableMap<ImmutableSet<ExecutionMarkable>, Integer> colors) {
        this.equivalenceClasses = equivalenceClasses;
        this.colors = colors;
    }

    public ImmutableMap<ExecutionMarkable, ImmutableSet<ExecutionMarkable>> getEquivalenceClasses() {
        return this.equivalenceClasses;
    }

    public ImmutableMap<ImmutableSet<ExecutionMarkable>, Integer> getColors() {
        return this.colors;
    }

    public Integer getColor(final ExecutionMarkable key) {
        return this.colors.get(this.equivalenceClasses.get(key));
    }

    public ExecutionStepColorization restrictTo(final Collection<List<? extends ExecutionMarkable>> executionSequences) {
        if (executionSequences.isEmpty()) {
            return ExecutionStepColorization.EMPTY;
        }

        final Set<ExecutionMarkable> retained = new HashSet<ExecutionMarkable>();

        for (final List<? extends ExecutionMarkable> executionSequence : executionSequences) {
            final Iterator<? extends ExecutionMarkable> sequenceIterator = executionSequence.iterator();

            ExecutionMarkable source = sequenceIterator.next();
            Map<ExecutionUid, ExecutionMarkable> sourceExecutionMarks = new LinkedHashMap<ExecutionUid, ExecutionMarkable>();
            source.collectExecutionMarks(sourceExecutionMarks);
            while (sequenceIterator.hasNext()) {
                final ExecutionMarkable target = sequenceIterator.next();
                final Map<ExecutionUid, ExecutionMarkable> targetExecutionMarks = new LinkedHashMap<ExecutionUid, ExecutionMarkable>();
                target.collectExecutionMarks(targetExecutionMarks);

                final Map<ExecutionUid, ExecutionMarkable> storedTargetExecMarks = new LinkedHashMap<ExecutionUid, ExecutionMarkable>(targetExecutionMarks);

                ExecutionStepColorization.cleanupExecutionMarks(sourceExecutionMarks, targetExecutionMarks);

                retained.addAll(sourceExecutionMarks.values());
                retained.addAll(targetExecutionMarks.values());

                source = target;
                sourceExecutionMarks = storedTargetExecMarks;
            }
        }

        final Map<ExecutionMarkable, ImmutableSet<ExecutionMarkable>> reducedRquivalenceClasses =
            new LinkedHashMap<ExecutionMarkable, ImmutableSet<ExecutionMarkable>>(this.equivalenceClasses);

        reducedRquivalenceClasses.keySet().retainAll(retained);

        return new ExecutionStepColorization(ImmutableCreator.create(reducedRquivalenceClasses), this.colors);
    }
}
