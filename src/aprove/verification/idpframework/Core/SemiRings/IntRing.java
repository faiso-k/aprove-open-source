package aprove.verification.idpframework.Core.SemiRings;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;

/**
 *
 * @author MP
 */
public interface IntRing<C extends IntRing<C>> extends PredefinedRing<C> {

    public int getBits();

    public C sign();

    public C unsign();

    @Override
    public ITerm<C> getTerm(IDPPredefinedMap predefinedMap);

    public C div(C other);
    public C mod(C other);
    public C gcd(C other);

    public C bitwiseAnd(C other);
    public C bitwiseOr(C other);
    public C bitwiseXor(C other);
    public C bitwiseNot();

}
