package aprove.verification.oldframework.Algebra.LimitPolynomials;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 * Encodes a single LVPConstraint into a set of SPCs yielding the constraint information, a set of SPCs yielding 0-1 conditions, plus a strictness SPC.
 * See below for encoding idea.
 * @author kabasci
 *
 */
public class LVPCToVPCEncoder {

    /**
     * Encodes a single LVPC into several SPCs, plus one strictness SPC. Note that we *ignore* the original constraint type!
     * @param constraint The constraint to encode
     * @return X: The constraints to satisfy; Y: The strictness constraint
     */
    /*
     * Encoding idea:
     *
     * First split the LVP into several LPs.
     * For each of the LPs, use the following algorithm:
     *
     *   For each exponent within the possible range test all monomials which can possibly have that exponent value
     *   on whether they have that exponent value. If they do, add them to this value's SPC of this variable.
     *
     *   Then add to each value's VPC a strictness coefficient. Each lower value's constraint is then disabled shall a higher strictness coefficient be set.
     *   The strictness constraint is the summ of all strictness coefficients of the constant part of the VPC.
     *
     *
     */
    public static Pair<List<SimplePolyConstraint>, SimplePolyConstraint> encodeSearchStrict(LimitVarPolynomialConstraint constraint) {

        // first split the LVPC by its variables, and treat them seperately.
        List<SimplePolyConstraint> result = new ArrayList<SimplePolyConstraint>();

        for (TRSVariable v: constraint.getPolynomial().getVariables())  {
            // The constraints have to hold greater or equal for all variable parts.
            result.addAll((constraint.getPolynomial().getVariablePart(v)).toConstraints(ConstraintType.GE));
        }

        Pair<List<SimplePolyConstraint>, SimplePolyConstraint>  res = ((constraint.getPolynomial().getConstantPart()).toConstraints());
        result.addAll(res.x);
        // Furthermore encode the constant part; here however we use the strictness constraints...

        return new Pair<List<SimplePolyConstraint>, SimplePolyConstraint>(result, res.y);
    }


}


