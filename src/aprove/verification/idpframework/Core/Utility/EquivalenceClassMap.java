package aprove.verification.idpframework.Core.Utility;

import java.util.*;

/**
 *
 * @author MP
 */
public class EquivalenceClassMap <T> {

    private final Map<T, Set<T>> map = new LinkedHashMap<T, Set<T>>();

    public Collection<Set<T>> getClasses() {
        return this.map.values();
    }

    public Set<T> getClass(final T element) {
        return this.map.get(element);
    }

    public Map<T, Set<T>> getClassMapping() {
        return this.map;
    }

    public void addElements(final Collection<? extends T> elements) {
        for (final T element : elements) {
            this.addElement(element);
        }
    }

    public void addElement(final T element) {
        if (!this.map.containsKey(element)) {
            final LinkedHashSet<T> eqClass = new LinkedHashSet<T>();
            eqClass.add(element);
            this.map.put(element, eqClass);
        }
    }

    public void mergeClasses(final Collection<T> elements) {
        if (!elements.isEmpty()) {
            final Iterator<T> iterator = elements.iterator();
            final T element1 = iterator.next();
            while (iterator.hasNext()) {
                final T element2 = iterator.next();
                this.mergeClasses(element1, element2);
            }
        }
    }

    public void mergeClasses(final T element1, final T element2) {
        final Set<T> class1 = this.map.get(element1);
        if (class1 == null) {
            throw new IllegalAccessError("element1 not in map, use addElement: " + element1);
        }

        final Set<T> class2 = this.map.get(element2);
        if (class2 == null) {
            throw new IllegalAccessError("element2 not in map, use addElement: " + element2);
        }

        if (class2 == class1) {
            return;
        }

        class1.addAll(class2);

        for (final T element : class2) {
            this.map.put(element, class1);
        }
    }

}
