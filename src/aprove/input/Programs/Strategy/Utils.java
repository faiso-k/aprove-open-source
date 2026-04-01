package aprove.input.Programs.Strategy;

import java.util.*;

import immutables.*;

public class Utils {

    private static ImmutableArrayList<? extends Immutable> empty =
        Utils.createFixedImmutableArrayList(new Immutable[0]);

    @SuppressWarnings("unchecked")
    public static <E extends Immutable> ImmutableArrayList<E> createFixedImmutableArrayList() {
        return (ImmutableArrayList<E>) Utils.empty;
    }

    public static <E extends Immutable> ImmutableArrayList<E> createFixedImmutableArrayList(E... elements) {
        ArrayList<E> al = new ArrayList<E>();
        for (E e : elements) {
            al.add(e);
        }
        return ImmutableCreator.create(al);
    }

}
