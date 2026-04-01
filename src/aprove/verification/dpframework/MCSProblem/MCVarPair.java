package aprove.verification.dpframework.MCSProblem;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Ordered pair of variables.
 *
 * @author fuhs
 */
public class MCVarPair implements Immutable, Exportable {
    private final TRSVariable smaller;
    private final TRSVariable greater;

    private MCVarPair(TRSVariable v1, TRSVariable v2) {
        int compare = v1.compareTo(v2);
        if (compare < 0) {
            this.smaller = v1;
            this.greater = v2;
        }
        else {
            this.smaller = v2;
            this.greater = v1;
        }
    }

    public static MCVarPair create(TRSVariable v1, TRSVariable v2) {
        return new MCVarPair(v1, v2);
    }

    public static Pair<MCVarPair, MCRelation> toEntry(TRSVariable v1, TRSVariable v2, MCRelation rel) {
        MCVarPair varPair = MCVarPair.create(v1, v2);
        MCRelation newRel = varPair.getFirst().equals(v1) ? rel : rel.invert();
        return new Pair<MCVarPair, MCRelation>(varPair, newRel);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result
                + ((this.greater == null) ? 0 : this.greater.hashCode());
        result = prime * result
                + ((this.smaller == null) ? 0 : this.smaller.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        MCVarPair other = (MCVarPair) obj;
        if (this.greater == null) {
            if (other.greater != null) {
                return false;
            }
        }
        else if (!this.greater.equals(other.greater)) {
            return false;
        }
        if (this.smaller == null) {
            if (other.smaller != null) {
                return false;
            }
        }
        else if (!this.smaller.equals(other.smaller)) {
            return false;
        }
        return true;
    }

    /**
     * @return the smaller
     */
    public TRSVariable getFirst() {
        return this.smaller;
    }

    /**
     * @return the greater
     */
    public TRSVariable getSecond() {
        return this.greater;
    }

    @Override
    public String export(Export_Util o) {
        return '(' + this.smaller.export(o) + ", "
                   + this.greater.export(o) + ')';
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }
}
