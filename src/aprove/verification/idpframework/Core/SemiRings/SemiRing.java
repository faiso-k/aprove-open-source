package aprove.verification.idpframework.Core.SemiRings;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import immutables.*;

/**
 * Contract: isZero() == true => hashCode() == 0 && equals(Arithmetic.ZERO) ==
 * true
 * @author Martin Pluecker
 */
public interface SemiRing<C extends SemiRing<C>> extends Immutable,
        SemiComparable<C>, IDPExportable, XmlExportable, GPolyCoeff {

    public C add(final C value);

    public C negate();

    public C subtract(final C value);

    public C mult(final C value);

    public C zero();

    public C one();

    public boolean isZero();

    public boolean isOne();

    public C getValue();

    public Integer signum();

    public boolean isSameRing(SemiRing<?> other);

    public String getDomainSuffix();

    public SemiRingDomain<C> createVarRange(C min, C max);

    public SemiRingDomain<C> createUnknownVarRange();

    public ITerm<C> getTerm(IDPPredefinedMap predefinedMap);

    public boolean isBoundedRing();

}
