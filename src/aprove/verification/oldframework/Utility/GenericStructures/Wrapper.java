package aprove.verification.oldframework.Utility.GenericStructures;

import java.io.*;

/**
 * @author thiemann
 *
 * A simple Wrapper of some type that can be used to store null values in
 * maps without having to call get and containsKey twice
 */
public class Wrapper<X> implements Serializable {

    private static final long serialVersionUID = -7865972536833306924L;

    public X x;

    public Wrapper(X x) {
        this.x = x;
    }

    @Override
    public boolean equals(Object other){
        if (other instanceof Wrapper) {
            Wrapper that = (Wrapper) other;

            if (this==that) {
                return true;
            }
            if (that == null) {
                return false;
            }

            if(this.x != that.x) {
                if (this.x == null) {
                    return false;
                }
                if (!this.x.equals(that.x)) {
                    return false;
                }
            }

            return true;
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return this.x == null ? "null" : this.x.toString();
    }

    @Override
    public int hashCode() {
        return this.x != null ? this.x.hashCode() : 0;
    }


}
