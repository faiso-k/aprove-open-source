package aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients;

import java.math.*;
import java.util.*;

/**
 * A factory for arctic integers.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class ArcticIntFactory extends ExoticIntFactory<ArcticInt> {

    /**
     * Cache previously generated ArcticInts for reuse, thus limiting
     * the number of objects that are created.
     */
    private final Map<BigInteger, ArcticInt> cache;

    private static ArcticIntFactory INSTANCE = null;

    private ArcticIntFactory() {
        this.cache = new HashMap<BigInteger, ArcticInt>();
    }

    public static ArcticIntFactory create() {
        if (ArcticIntFactory.INSTANCE == null) {
            ArcticIntFactory.INSTANCE = new ArcticIntFactory();
        }
        return ArcticIntFactory.INSTANCE;
    }

    @Override
    public ArcticInt create(BigInteger i) {
        if (this.cache.containsKey(i)) {
            return this.cache.get(i);
        }
        ArcticInt newInstance = ArcticInt.create(i);
        this.cache.put(i, newInstance);
        return newInstance;
    }

    @Override
    public ArcticInt create(int i) {
        return this.create(BigInteger.valueOf(i));
    }

    @Override
    public ArcticInt fromInteger(BigInteger from) {
        return this.create(from);
    }
    @Override
    public ArcticInt one() {
        return ArcticInt.ONE;
    }

    @Override
    public ArcticInt zero() {
        return ArcticInt.ZERO;
    }
}
