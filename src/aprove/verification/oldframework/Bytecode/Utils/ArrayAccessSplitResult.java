package aprove.verification.oldframework.Bytecode.Utils;

import org.json.*;

/**
 * If we cannot refine the state to compute if we need to throw an
 * IndexOutOfBoundsException/ArrayStoreException, we use this to just
 * decide for all cases.
 * @author Marc Brockschmidt
 */
public class ArrayAccessSplitResult implements SplitResult {
    /**
     * Marks that we need to do an IOOBException;
     */
    private final Boolean needsIOOBException;

    /**
     * Marks that we need to do an ArrayStoreException;
     */
    private final Boolean needsArrayStoreException;

    /**
     * Create a new SplitResult for some integer comparison.
     * @param needsIOOBExc Marks that we need to do an IOOBException
     * @param needsArrayStoreExc Marks that we need to do an ArrayStoreException
     */
    public ArrayAccessSplitResult(final Boolean needsIOOBExc, final Boolean needsArrayStoreExc) {
        this.needsIOOBException = needsIOOBExc;
        this.needsArrayStoreException = needsArrayStoreExc;
    }

    /**
     * @return true iff we need to do an IOOBException;
     */
    public Boolean needsIOOBException() {
        return this.needsIOOBException;
    }

    /**
     * @return true iff we need to do an ArrayStoreException;
     */
    public Boolean needsArrayStoreException() {
        return this.needsArrayStoreException;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb);
        return sb.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void toString(final StringBuilder sb) {
        sb.append("Array Store Result: (IOOBExc "
            + this.needsIOOBException
            + ", AStoreExc "
            + this.needsArrayStoreException + ")");
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Split Type", "Array Access");
        res.put("Needs IndexOutOfBoundsException", this.needsIOOBException);
        res.put("Needs Array Store Exception", this.needsArrayStoreException);
        return res;
    }
}
