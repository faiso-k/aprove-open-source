/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfFunctions.domains;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;
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

    /**
     * Cached Domain instances. It is assumed that a problem does not contain
     * more than 20 different domains (if generated from a real program,
     * z, 8, 16, 32, 64 should be all).
     *
     * Maybe raise this limit if we are to implement signed and unsigned domains.
     *
     * FIXME: Must we be synchronized?
     */
    private static Map<String, Domain> domainMap =
        Collections.synchronizedMap(new LRUCache<String, Domain>(20));

    public static final IntegerDomain INTEGERS = DomainFactory.createIntDomain(0);
    public static final ImmutableList<IntegerDomain> INTEGER_INTEGER;
    static {
        ArrayList<IntegerDomain> list = new ArrayList<IntegerDomain>(2);
        list.add(DomainFactory.INTEGERS);
        list.add(DomainFactory.INTEGERS);
        INTEGER_INTEGER = ImmutableCreator.create(list);
    }

    public static final BooleanDomain BOOLEAN = BooleanDomain.createNew();
    public static final ImmutableList<BooleanDomain> BOOLEAN_BOOLEAN;
    static {
        ArrayList<BooleanDomain> list = new ArrayList<BooleanDomain>(2);
        list.add(DomainFactory.BOOLEAN);
        list.add(DomainFactory.BOOLEAN);
        BOOLEAN_BOOLEAN = ImmutableCreator.create(list);
    }


    public static IntegerDomain createIntDomain(int bits) {
        String suffix = IntegerDomain.generateSuffix(bits);
        IntegerDomain dom = (IntegerDomain) DomainFactory.domainMap.get(suffix);
        if (dom != null) {
            return dom;
        }

        dom = IntegerDomain.createNew(bits);
        if (dom != null) {
            DomainFactory.domainMap.put(suffix, dom);
        }

        return dom;
    }



}
