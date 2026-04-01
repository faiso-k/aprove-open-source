package aprove.verification.oldframework.Algebra.Orders.Utility ;

/** A set with exactly two elements.
 *  Elements have to satisfy:
 *  x.equals(y) ==> x.hashCode()==y.hashCode()
 *
 *  @author      Stephan Falke
 *  @version $Id$
 */

public class Doubleton<T> {

    private T x;
    private T y;
    private int hash;
    private String strRep;
    private boolean sameHash;

    private Doubleton(T x, T y) {
        this.sameHash = false;
        int xHash = x.hashCode();
        int yHash = y.hashCode();
        if(xHash != yHash) {
            /* x is the element which has the smaller hash code */
            if(xHash < yHash) {
                this.x = x;
                this.y = y;
            }
            else {
                this.x = y;
                this.y = x;
            }
            this.strRep = "{" + this.x.toString() + ", " + this.y.toString() + "}";
            this.hash = this.strRep.hashCode();
        }
        else {
            /* same hash */
            this.sameHash = true;
            this.x = x;
            this.y = y;
            this.strRep = "{" + this.x.toString() + ", " + this.y.toString() + "}";
            String strRep2 = "{" + this.y.toString() + ", " + this.x.toString() + "}";
            this.hash = Math.min(this.strRep.hashCode(), strRep2.hashCode());
        }
    }

    /** Creates an instance of <code>Doubleton</code> consisting of the elements
     * <code>x</code> and <code>y</code>.
     * @param x  one element
     * @param y  another element
     */
    public static <T> Doubleton<T> create(T x, T y) {
    return new Doubleton<T>(x, y);
    }

    @Override
    public String toString() {
    return this.strRep;
    }

    @Override
    public int hashCode() {
    return this.hash;
    }

    @Override
    public boolean equals(Object o) {
    Doubleton other;
    try {
        other = (Doubleton)o;
    }
    catch(ClassCastException e) {
        return false;
    }
    return this.x.equals(other.x) && this.y.equals(other.y)
            || (this.sameHash && this.x.equals(other.y) && this.y.equals(other.x));
    }

}
