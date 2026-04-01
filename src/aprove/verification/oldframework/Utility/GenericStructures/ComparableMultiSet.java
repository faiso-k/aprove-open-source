package aprove.verification.oldframework.Utility.GenericStructures;


public class ComparableMultiSet<T extends Comparable<T>> extends HashMultiSet<T>
    implements
        Comparable<ComparableMultiSet<T>>
{
    @Override
    public int compareTo(final ComparableMultiSet<T> o) {
        // TODO Auto-generated method stub
        return 0;
    }
}
