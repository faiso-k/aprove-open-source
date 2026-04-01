package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

/** Hashtable that hashes over a pair of objects.
 *
 *  @author      Stephan Falke
 *  @version $Id$
 */

public class DoubleHash<T,U,V> implements java.io.Serializable{

    private Hashtable<T,Hashtable<U,V>> hash;


    /* constructors */

    private DoubleHash() {
    this.hash = new Hashtable<T,Hashtable<U,V>>();
    }

    /** Creates a new instance of <code>DoubleHash</code>.
     */
    public static <W,X,Y> DoubleHash<W,X,Y> create() {
    return new DoubleHash<W,X,Y>();
    }

    /** Maps the pair <code>(s, t)</code> to <code>value</code>.
     */
    public void put(T s, U t, V value) {
    Hashtable<U,V> sHash;

    sHash = this.hash.get(s);
    if(sHash==null) {
        sHash = new Hashtable<U,V>();
        this.hash.put(s, sHash);
    }

    sHash.put(t, value);
    }

    /** Returns the element that <code>(s, t)</code> is mapped to.
     */
    public V get(T s, U t) {
    Hashtable<U,V> sHash = this.hash.get(s);
    if(sHash!=null) {
        return sHash.get(t);
    }
    return null;
    }

}
