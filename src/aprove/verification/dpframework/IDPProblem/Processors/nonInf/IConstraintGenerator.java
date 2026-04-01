/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf;

import java.util.*;

import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public interface IConstraintGenerator {

    /**
     * @return w: the constraints, x: the proof, y: variable values which became clear during generation (for optimization), z: stored implications before poly level
     *
     */
    Quadruple<OrderPolyConstraint<BigIntImmutable>, IConstraintGeneratorProof, Map<GPolyVar, BigIntImmutable>, Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>>> generateContraints(
            IDPProblem idp, IdpQUsableRules usableRules,
            IDPGInterpretation interpretation,
            StrictMode strictMode, GInterpretationMode<BigIntImmutable> form,
            OPCRange<BigIntImmutable> boolRange, Abortion aborter) throws AbortionException;


    /**
     * @return w: the usable rules constraints, x: the constraints for each DP, y: the proof, z: variable values which became clear during generation (for optimization)
     *
     */
    Quadruple<OrderPolyConstraint<BigIntImmutable>, Map<GeneralizedRule, OrderPolyConstraint<BigIntImmutable>>, IConstraintGeneratorProof, Map<GPolyVar, BigIntImmutable>> validate(
            IDPProblem idp, IdpQUsableRules usableRules,
            IDPGInterpretation interpretation,
            Map<GeneralizedRule,Map<List<GeneralizedRule>,List<Implication>>> savedConstraintSetProRule,
            Abortion aborter) throws AbortionException;

    public static interface IConstraintGeneratorProof extends Proof {

    }

}
