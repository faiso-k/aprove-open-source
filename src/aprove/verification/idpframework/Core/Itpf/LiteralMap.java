package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.verification.oldframework.Logic.*;

/**
 * @author Martin Pluecker
 */
public class LiteralMap extends LinkedHashMap<ItpfAtom, Boolean> {

    private boolean unsatisfiable = false;

    public LiteralMap() {
        this(false);
    }

    public LiteralMap(final boolean unsatisfiable) {
        this.unsatisfiable = unsatisfiable;
    }

    public LiteralMap(final Map<? extends ItpfAtom, Boolean> takeFrom) {
        this(false);
        for (final Map.Entry<? extends ItpfAtom, Boolean> entry : takeFrom.entrySet()) {
            this.put(entry.getKey(), entry.getValue());
        }
    }

    public LiteralMap(final Collection<? extends ItpfAtom> keys, final Boolean value) {
        this(false);
        this.putAll(keys, value);
    }

    public LiteralMap(final ItpfAtom atom, final Boolean value) {
        this(false);
        this.put(atom, value);
    }

    @Override
    public Boolean put(final ItpfAtom key, final Boolean value) {
        if (value == null) {
            throw new IllegalArgumentException("value must not be null");
        }

        final YNM keyTrivial = key.isTrivial();
        if (keyTrivial == YNM.YES && value) {
            return null;
        } else if (keyTrivial == YNM.NO && !value) {
            return null;
        }

        final Boolean oldRes = super.put(key, value);
        if (oldRes != null) {
            if (!oldRes.equals(value)) {
                this.unsatisfiable = true;
            }
        }
        return oldRes;
    }

    public Boolean putAll(final Collection<? extends ItpfAtom> keys, final Boolean value) {
        boolean res = false;

        for (final ItpfAtom key : keys) {
            final Boolean putRes = this.put(key, value);
            res = res || (putRes != null && putRes);
        }

        return res;
    }

    public boolean isUnsatisfiable() {
        return this.unsatisfiable;
    }

    public void unsatisfiable() {
        this.unsatisfiable = true;
    }

}
