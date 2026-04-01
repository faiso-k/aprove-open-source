package aprove.verification.dpframework.Utility;

import java.util.*;

import immutables.*;

/**
 * NameProvider which wraps a collection: A name is contained
 * in the NameProvider iff it is contained in the collection.
 */
public class CollectionNameProvider implements NameProvider, Immutable {
    public final Set<String> names;

    protected CollectionNameProvider(Set<String> names) {
        this.names = names;
    }

    public static CollectionNameProvider create(ImmutableSet<String> names) {
        return new CollectionNameProvider(names);
    }

    public static CollectionNameProvider create(Collection<String> names) {
        return new CollectionNameProvider(new HashSet<String>(names));
    }

    @Override
    public boolean contains(String name) {
        return this.names.contains(name);
    }
}
