package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

import java.math.*;
import java.util.*;

/**
 * A factory for tropical integers.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class TropicalIntFactory extends ExoticIntFactory<TropicalInt> {

    /**
     * Cache previously generated TropicalInts for reuse,
     * thus limiting the number of objects that are created.
     */
    private final Map<BigInteger, TropicalInt> cache;

    private static TropicalIntFactory INSTANCE = null;

    private TropicalIntFactory() {
        this.cache = new HashMap<BigInteger, TropicalInt>();
    }

    public static TropicalIntFactory create() {
        if (TropicalIntFactory.INSTANCE == null) {
            TropicalIntFactory.INSTANCE = new TropicalIntFactory();
        }
        return TropicalIntFactory.INSTANCE;
    }

    @Override
    public TropicalInt create(BigInteger i) {
        if (this.cache.containsKey(i)) {
            return this.cache.get(i);
        }
        TropicalInt newInstance = TropicalInt.create(i);
        this.cache.put(i, newInstance);
        return newInstance;
    }

    @Override
    public TropicalInt create(int i) {
        return this.create(BigInteger.valueOf(i));
    }

    @Override
    public TropicalInt fromInteger(BigInteger from) {
        return this.create(from);
    }
    @Override
    public TropicalInt one() {
        return TropicalInt.ONE;
    }

    @Override
    public TropicalInt zero() {
        return TropicalInt.ZERO;
    }
}