package aprove.verification.idpframework.Core.Utility.Marking;

import java.util.*;

import aprove.verification.idpframework.Core.*;
import immutables.*;




/**
 *
 * @author MP
 * @param <T>
 */
public interface MarkContent<C extends MarkContent<C, T>, T>  extends Iterable<T>, Immutable {

    public boolean isEmpty();
    public int size();
    public ImmutableCollection<T> asCollection();

    public boolean isSingleton(T content);

    public static abstract class MarkContentSkeleton<C extends MarkContent<C, T>, T> extends IDPExportable.IDPExportableSkeleton implements MarkContent<C, T> {

        protected final ImmutableCollection<T> items;

        public MarkContentSkeleton(final ImmutableCollection<T> items) {
            this.items = items;
        }

        @Override
        public int size() {
            return this.items.size();
        }

        @Override
        public Iterator<T> iterator() {
            return this.items.iterator();
        }

        @Override
        public ImmutableCollection<T> asCollection() {
            return this.items;
        }

        @Override
        public boolean isEmpty() {
            return this.items.isEmpty();
        }

        @Override
        public boolean isSingleton(final T content) {
            return this.items.size() == 1 && this.items.iterator().next().equals(content);
        }

    }

}
