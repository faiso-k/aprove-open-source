package aprove.verification.oldframework.Utility.GenericStructures;

import java.util.*;

import org.json.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.JSON.*;

/**
 * @author thiemann
 *
 * A simple Pair, can be used to build ListOfMapEntries
 * such that we can iterate over "duplicating Maps"
 * @param <X> The type of the first component.
 * @param <Y> The type of the second component.
 */
public class Pair<X, Y> implements Map.Entry<X, Y>, java.io.Serializable, JSONExport, Exportable {

    /**
     * For serialization.
     */
    private static final long serialVersionUID = 2560465779872229035L;

    public static <Z> void flip(final Pair<Z, Z> pair) {
        final Z key = pair.getKey();
        final Z value = pair.getValue();
        pair.setValue(key);
        pair.setKey(value);
    }

    public X x;

    public Y y;

    public Pair(final X key, final Y value) {
        this.x = key;
        this.y = value;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final Pair other = (Pair) obj;
        if (this.x == null) {
            if (other.x != null) {
                return false;
            }
        } else if (!this.x.equals(other.x)) {
            return false;
        }
        if (this.y == null) {
            if (other.y != null) {
                return false;
            }
        } else if (!this.y.equals(other.y)) {
            return false;
        }
        return true;
    }

    @Override
    public X getKey() {
        return this.x;
    }

    @Override
    public Y getValue() {
        return this.y;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.x == null) ? 0 : this.x.hashCode());
        result = prime * result + ((this.y == null) ? 0 : this.y.hashCode());
        return result;
    }

    public X setKey(final X key) {
        final X old = this.x;
        this.x = key;
        return old;
    }

    @Override
    public Y setValue(final Y value) {
        final Y old = this.y;
        this.y = value;
        return old;
    }

    /**
     * @author Sebastian Weise
     */
    public Pair<X, Y> shallowCopy() {
        return new Pair<X, Y>(this.x, this.y);
    }

    @Override
    public JSONArray toJSON() {
        return new JSONArray(new Object[]{JSONExportUtil.toJSON(this.x), JSONExportUtil.toJSON(this.y)});
    }

    @Override
    public String toString() {
        return "(" + (this.x == null ? "null" : this.x.toString()) + ","
            + (this.y == null ? "null" : this.y.toString()) + ")";
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder();
        
        sb.append('(');
        if (x instanceof Exportable) {
            sb.append(((Exportable) x).export(eu));
        } else {
            sb.append(x.toString());
        }
        sb.append(',');
        if (y instanceof Exportable) {
            sb.append(((Exportable) y).export(eu));
        } else {
            sb.append(y.toString());
        }
        sb.append(')');
        
        return sb.toString();
    }

}
