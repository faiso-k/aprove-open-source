package aprove.verification.dpframework.BasicStructures;

/**
 * Can be turned into a TRSTerm.
 * @author cryingshadow
 * @version $Id$
 */
public interface TRSTermExpressible {

    /**
     * @return A TRSTerm representation of this.
     */
    TRSTerm toTerm();

}
