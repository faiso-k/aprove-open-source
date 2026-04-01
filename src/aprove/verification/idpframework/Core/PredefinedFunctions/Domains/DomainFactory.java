/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions.Domains;

import java.util.*;
import java.util.concurrent.*;

import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import immutables.*;

/**
 * Factory for Domains.
 *
 * <p>As there will be probably only a handful of really different Domain
 * instances, provide an facility to cache those instances.</p>
 *
 * <p>This factory is threadsafe.</p>
 * @author noschinski
 *
 */
public class DomainFactory {

    public static final String SUFFIX_SEPERATOR = "@";

    public static final UnknownDomain UNKNOWN = UnknownDomain.createNew();

    public static final IntegerDomain<BigInt> INTEGERS = new IntegerDomain<BigInt>(BigInt.ZERO, null, null);

    private static final ConcurrentHashMap<UserDefinedDomain, UserDefinedDomain> userDefinedDomains = new ConcurrentHashMap<UserDefinedDomain, UserDefinedDomain>();

    public static final ImmutableList<IntegerDomain<BigInt>> INTEGER;
    static {
        final ArrayList<IntegerDomain<BigInt>> list = new ArrayList<IntegerDomain<BigInt>>(1);
        list.add(DomainFactory.INTEGERS);
        INTEGER = ImmutableCreator.create(list);
    }

    public static final ImmutableList<IntegerDomain<BigInt>> INTEGER_INTEGER;
    static {
        final ArrayList<IntegerDomain<BigInt>> list = new ArrayList<IntegerDomain<BigInt>>(2);
        list.add(DomainFactory.INTEGERS);
        list.add(DomainFactory.INTEGERS);
        INTEGER_INTEGER = ImmutableCreator.create(list);
    }

    public static final BooleanDomain BOOLEANS = BooleanDomain.BOOLEAN;

    public static final ImmutableList<BooleanDomain> BOOLEAN;
    static {
        final ArrayList<BooleanDomain> list = new ArrayList<BooleanDomain>(1);
        list.add(DomainFactory.BOOLEANS);
        BOOLEAN = ImmutableCreator.create(list);
    }

    public static final ImmutableList<BooleanDomain> BOOLEAN_BOOLEAN;
    static {
        final ArrayList<BooleanDomain> list = new ArrayList<BooleanDomain>(2);
        list.add(DomainFactory.BOOLEANS);
        list.add(DomainFactory.BOOLEANS);
        BOOLEAN_BOOLEAN = ImmutableCreator.create(list);
    }

    public static IntegerDomain<BigInt> createUnknownVarRange(final BigInt ring) {
        return new IntegerDomain<BigInt>(BigInt.ZERO, null, null);
    }

    public static IntegerDomain<BigInt> createVarRange(final BigInt ring, final BigInt min, final BigInt max) {
        return new IntegerDomain<BigInt>(BigInt.ZERO, min, max);
    }

    public static IntegerDomain<BigInt> positiveVarRange(final BigInt ring) {
        return new IntegerDomain<BigInt>(BigInt.ZERO, BigInt.ZERO, null);
    }

    public static IntegerDomain<BigInt> negativeVarRange(final BigInt ring) {
        return new IntegerDomain<BigInt>(BigInt.ZERO, null, null);
    }

    public static UserDefinedDomain createUserDefinedDomain(final int id,
        final ImmutableSet<SemiRingDomain<?>> specializations) {
        UserDefinedDomain dom = new UserDefinedDomain(id, specializations);
        dom = ConcurrentUtil.addToCache(DomainFactory.userDefinedDomains, dom, dom);
        return dom;
    }

}
