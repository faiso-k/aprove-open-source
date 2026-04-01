/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class SortNatPoly {

    /**
     * Sorts a GPoly into two positive polys
     * @param interpretation
     * @param coeff The coef that should be sorted
     * @return A pair of polys, the left poly contains the positive part, the right one contains
     * the negative parts.
     */
    public static Pair<GPoly<BigIntImmutable, GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> sort(GInterpretation<BigIntImmutable> interpretation, GPoly<BigIntImmutable, GPolyVar> coeff) {
        if (!coeff.isFlat(interpretation.getRing(), interpretation.getMonoid())) {
            coeff = interpretation.getFvInner().applyTo(coeff);
        }
        Set<GPoly<BigIntImmutable, GPolyVar>> left = new LinkedHashSet<GPoly<BigIntImmutable, GPolyVar>>();
        Set<GPoly<BigIntImmutable, GPolyVar>> right = new LinkedHashSet<GPoly<BigIntImmutable, GPolyVar>>();
        GPolyFactory<BigIntImmutable, GPolyVar> factory = interpretation.getFactory().getInnerFactory();
        Semiring<BigIntImmutable> ring = interpretation.getRing();
        for (Map.Entry<GMonomial<GPolyVar>, BigIntImmutable> entry : coeff.getMonomials(interpretation.getRing(), interpretation.getMonoid()).entrySet()) {
            Collection<GPolyVar> vars = new ArrayList<GPolyVar>();
            for (Map.Entry<GPolyVar, BigInteger> varEntry : entry.getKey().getExponents().entrySet()) {
                for (int i = varEntry.getValue().intValue()-1; i>=0; i--) {
                    vars.add(varEntry.getKey());
                }
            }
            if (entry.getValue().getBigInt().signum() >= 0) {
                left.add(factory.concat(entry.getValue(), factory.buildVariables(vars)));
            } else {
                right.add(factory.concat(BigIntImmutable.create(entry.getValue().getBigInt().negate()), factory.buildVariables(vars)));
            }
        }
        return new Pair<GPoly<BigIntImmutable, GPolyVar>, GPoly<BigIntImmutable, GPolyVar>>(
                left.size() > 0 ? factory.plus(left) : factory.buildFromCoeff(((Ring<BigIntImmutable>)ring).zero()),
                right.size() > 0 ? factory.plus(right) : factory.buildFromCoeff(((Ring<BigIntImmutable>)ring).zero()));
    }

}
