/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

@Deprecated
/**
 * To be implemented
 */
public class InfRulePolyBGraphFlow extends InfRulePolyBAbstract {

    @Override
    public InfRuleID getID() {
        return InfRuleID.IDP_SMT_SPLIT;
    }

    @Override
    public String getLongName() {
        return "IDP_POLY_B graphFlow: create all cases x >= 0, x < 0";
    }

    @Override
    public String getName() {
        return "IDP_POLY_B graphFlow";
    }

    @Override
    protected GPolyVar decideNextSplit(
        Implication implication,
        GInterpretation<BigIntImmutable> interpretation,
        Map<GPolyVar, VarAnalysis> varAnalysis,
        Set<Set<MonomialAnalysis>> useableConstraints,
        Set<GPolyVar> remainingVariable)
    {
        throw new UnsupportedOperationException("To be implemented");
    }

}
