package aprove.verification.idpframework.Polynomials.Interpretation;

import immutables.*;

/**
 *
 * @author MP
 */
public class BooleanPolyVarKey implements Immutable {

    public final BooleanPolyVarKeyable key;
    public final Immutable metaData;
    private final int hashCode;

    public BooleanPolyVarKey(final BooleanPolyVarKeyable key, final Immutable metaData) {
        this.key = key;
        this.metaData = metaData;

        final int prime = 31;
        int result = 1;
        result = prime * result + key.hashCode();
        result =
            prime * result + ((metaData == null) ? 0 : metaData.hashCode());

        this.hashCode = result;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

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
        final BooleanPolyVarKey other = (BooleanPolyVarKey) obj;
        if (this.metaData == null) {
            if (other.metaData != null) {
                return false;
            }
        } else if (!this.metaData.equals(other.metaData)) {
            return false;
        }
        return this.key.equals(other.key);
    }
}
