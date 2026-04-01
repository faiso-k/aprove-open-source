package aprove.verification.idpframework.Core.Utility.Marking;

import java.util.*;
import java.util.logging.*;

import immutables.*;

/**
 * @author Martin Pluecker
 */
public class MarksHandler<ResultType extends MarkContent<ResultType, R>, M extends Markable<ResultType, M, R>, R>
        implements Markable<ResultType, M, R> {

    private static Logger log = Logger.getLogger("aprove.verification.idpframework.Core.Utility.Marking.MarksHandler");

    /*
    public static <T extends SelfMarkable<R, T>, R extends MarkContent<R, T>> void setMark(final Mark mark, final T original,
        final T modified,
        final ApplicationMode mode) {
        setMark(mark, original, modified.getSelfMark(), mode);
    }*/

    public static <T extends SelfMarkable<R, T>, R extends MarkContent<R, T>, MetaDataType> void setExecutionMark(final ExecutionMark<MetaDataType> mark, final T original,
        final R modified) {

        original.getMarks().setMark(mark, modified);
        if (mark.isCompatible(mark)) {
            for (final T modifiedObject : modified) {
                modifiedObject.getMarks().setMark(mark,
                    modifiedObject.getSelfMark());
            }
        }

        if (!modified.isSingleton(original)) {
            for (final T modifiedObject : modified) {
                original.getMarks().copyCompatibleMarks(modifiedObject, mark);
            }
        }
    }

    public static <MetaDataType> boolean isMarkedFail(final Mark<MetaDataType> mark, final Markable<?, ?, ?> c) {
        final ImmutablePair<? extends MarkContent<?, ?>, ?> markData = c.getMarks().getMark(mark);
        return markData != null && markData.x.size() == 1
            && c.equals(markData.x.iterator().next());
    }

    /**
     * Map from mark to meta data.
     */
    private final Map<Mark<?>, ImmutablePair<ResultType, ?>> marks;
    private final Markable<ResultType, M, R> source;

    /**
     * Default costructor.
     */
    public MarksHandler(final Markable<ResultType, M, R> source) {
        this.marks = new LinkedHashMap<Mark<?>, ImmutablePair<ResultType, ?>>();
        this.source = source;
    }

    /**
     * @param mark The mark.
     * @return true iff object is marked with mark.
     */
    public boolean isMarked(final Mark<?> mark) {
        synchronized (this.marks) {
            return this.marks.containsKey(mark);
        }
    }


    /**
    /**
     * @param mark The mark.
     * @param metaData The meta data.
     */
    public <MetaDataType> void setMark(final Mark<MetaDataType> mark, final ResultType metaData) {
        synchronized (this.marks) {
            this.marks.put(mark, new ImmutablePair<ResultType, MetaDataType>(metaData, null));
        }
    }

    /**
     * @param mark The mark.
     * @param metaData The meta data.
     */
    public <MetaDataType> void setMark(final Mark<MetaDataType> mark,
        final ImmutablePair<ResultType, MetaDataType> metaData) {
        synchronized (this.marks) {
            this.marks.put(mark, metaData);
        }
    }

    /**
     * @param mark The mark.
     * @param metaData The meta data.
     */
    public <MetaDataType> void setMark(final Mark<MetaDataType> mark,
        final ResultType metaData,
        final MetaDataType proof) {
        synchronized (this.marks) {
            this.marks.put(mark, new ImmutablePair<ResultType, MetaDataType>(metaData, proof));
        }
    }

    /**
     * @param mark The mark.
     * @return The mark's meta data.
     */
    @SuppressWarnings("unchecked")
    public <MetaDataType> ImmutablePair<ResultType, MetaDataType> getMark(final Mark<MetaDataType> mark) {
        synchronized (this.marks) {
            return (ImmutablePair<ResultType, MetaDataType>) this.marks.get(mark);
        }
    }

    /*
    /**
     * MAKE SURE TO SYNCHRONIZE OVER MARKS
     * @return
    Map<ItpfMark<? extends Object>, Object> getMarks() {
        return marks;
    }
     */

    /**
     * @param target Target handler the marks must be copied to.
     */
//    public void copyAtomicMarks(final Markable<ResultType, M, R> target) {
//        synchronized (marks) {
//            final Map<Mark<?>, ImmutablePair<ResultType, ?>> targetMarks =
//                target.getMarks().marks;
//            synchronized (targetMarks) {
//                for (final Map.Entry<Mark<?>, ImmutablePair<ResultType, ?>> mark : marks.entrySet()) {
//                    if (mark.getKey().isAtomicMark()) {
//                        targetMarks.put(mark.getKey(), mark.getValue());
//                    }
//                }
//            }
//        }
//    }

    public <S extends SelfMarkable<Rst, S>, Rst extends MarkContent<Rst, S>, MetaDataType> void copyCompatibleMarks(final S target,
        final Mark<MetaDataType> newMark) {
        this.copyCompatibleMarks(target, Collections.singleton(newMark));
    }

    public <S extends SelfMarkable<Rst, S>, Rst extends MarkContent<Rst, S>, MetaDataType> void copyCompatibleMarks(final Collection<S> targets,
        final Mark<MetaDataType> newMark) {
        for (final SelfMarkable<Rst, ?> target : targets) {
            this.copyCompatibleMarks(target, Collections.singleton(newMark));
        }
    }

    /**
     * Copies all marks which are compatible to a given new marks to the target.
     * @param <R>
     * @param <M, R>
     * @param target Target handler the marks must be copied to.
     * @param newMark The new marks the copied marks must be compatible to.
     */
    public <Rst extends MarkContent<Rst, G>, G, MetaDataType> void copyCompatibleMarks(final SelfMarkable<Rst, ?> target,
        final Collection<Mark<MetaDataType>> newMarks) {
        if (this.source instanceof SelfMarkable<?, ?>) {
            @SuppressWarnings("unchecked")
            final R selfMarkableSource = (R) this.source;
            synchronized (this.marks) {
                final Map<Mark<?>, ImmutablePair<Rst, ?>> targetMarks =
                    target.getMarks().marks;
                synchronized (targetMarks) {
                    for (final Map.Entry<Mark<?>, ImmutablePair<ResultType, ?>> markResult : this.marks.entrySet()) {
                        if (markResult.getValue().x.isSingleton(selfMarkableSource)) {
                            boolean compatible = true;
                            for (final Mark<?> newMark : newMarks) {
                                if (!markResult.getKey().equals(newMark) && !markResult.getKey().isCompatible(newMark)) {
                                    compatible = false;
                                    if ((newMark.toString().indexOf("FilterFreeVariables")) <= 0) {
                                        MarksHandler.log.finest("MARK: dropped fail of [" + markResult.getKey() + "] due to new mark [" + newMark + "] @ " + target.hashCode());
                                    }
                                    break;
                                }
                            }

                            if (compatible) {
                                final Rst singleton =
                                    target.getSelfMark();
                                targetMarks.put(markResult.getKey(), new ImmutablePair<Rst, MetaDataType>(singleton, null));
                            }
                        }
                    }
                }
            }
        }
    }

    @Override
    public MarksHandler<ResultType, M, R> getMarks() {
        return this;
    }


}
