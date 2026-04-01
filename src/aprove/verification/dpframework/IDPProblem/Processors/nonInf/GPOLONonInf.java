/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf;

import java.math.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.orders.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.IConstraintGenerator.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.IDPGInterpretation.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

public class GPOLONonInf extends GPOLOINT implements INonInfOrder {

    private final IDPGInterpretation idpGInterpretation;
    private final IConstraintGeneratorProof constraintsProof;

    public GPOLONonInf(IDPGInterpretation interpretation,
            IConstraintGeneratorProof constraintGeneratorProof) {
        super(interpretation);
        this.idpGInterpretation = interpretation;
        this.constraintsProof = constraintGeneratorProof;
    }

    @Override
    public boolean orientsStrictly(GeneralizedRule rule) {
        BigIntImmutable value = this.idpInterpretation.getBoolConstantValue(ConstantType.StrictOrientation, rule);
        if (value == null) {
            return false;
        }
        return value.getBigInt().signum() > 0;
    }

    @Override
    public boolean nonInf_lhsGEConst(GeneralizedRule rule) {
        if (this.idpInterpretation.isTupleNat()) {
            return true;
        }
        BigIntImmutable value = this.idpInterpretation.getBoolConstantValue(ConstantType.CompareToNonInfConstant, rule);
        if (value != null) {
            return value.getBigInt().compareTo(BigInteger.ZERO) > 0;
        } else {
            if (!this.idpInterpretation.getHasInitializedBoolConstant(ConstantType.CompareToNonInfConstant, rule)) {
                return true;
            } else {
                return false;
            }
        }
    }

    @Override
    public IConstraintGeneratorProof getConstraintsProof() {
        return this.constraintsProof;
    }

    @Override
    public IDPGInterpretation getInterpretation() {
        return this.idpGInterpretation;
    }
}
