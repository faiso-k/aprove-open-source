package aprove.verification.oldframework.Utility.GenericStructures;


/**
 * @author rabe
 *
 * Class reprents a pair which is comparable based on the lexicographical combination of
 * its components
 */
public  class ComparablePair<X extends Comparable, Y extends Comparable> extends Pair<X,Y> implements Comparable {

    public ComparablePair(X key, Y value) {
        super(key, value);
    }

    @Override
    public  int compareTo(Object o) {

        ComparablePair that = (ComparablePair)o;

        if( this.getKey().compareTo(that.getKey() ) == 0){
            return this.getValue().compareTo(that.getValue());
        }

        return this.getKey().compareTo(that.getKey());

    }

}
