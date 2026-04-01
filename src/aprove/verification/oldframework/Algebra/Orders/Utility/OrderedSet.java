package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** Abstract implementation of an Ordered Set.
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public abstract class OrderedSet<T> implements Exportable, DOT_Able, SizeMeasure {
    protected List<T> set;
    protected int size;
    protected boolean[] relation;

    public OrderedSet() {
    }

    /* relation[i + size*j] == true  iff  elem_i > elem_j */

    public List<T> getSet() {
        return this.set;
    }

    /** Returns <code>true</code> if <code>l</code> > <code>r</code> in
     * this poset, <code>false</code> otherwise.
     */
    public boolean isGreater(T l, T r) {
        return this.relation[this.set.indexOf(l)
                + this.size*this.set.indexOf(r)];
    }

    /** Returns the list of all pairs (t, u) with t > u.
     */
    public List<Pair<T, T>> getStrictPairs() {

        List<Pair<T, T>> result = new ArrayList<Pair<T, T>>();
        for (T t :  this.set) {
            for (T u : this.set) {
                if (t != u && this.isGreater(t, u)) {
                    result.add(new Pair<T, T>(t, u));
                }
            }
        }
        return result;
    }

    public abstract void setGreater(T l, T r) throws OrderedSetException;

    public abstract void setEquivalent(T l, T r) throws OrderedSetException;

    public abstract Map<T,Integer> getTopSortMap();

    @Override
    public int hashCode() {
        return this.toHashString().hashCode();
    }

    public abstract String toHashString();
    @Override
    public abstract String toDOT();
    @Override
    public abstract String export(Export_Util eu);


    @Override
    public int getSizeMeasure(){
        return this.size;
    }

}
