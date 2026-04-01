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

public class InfRulePolyBSimple extends InfRulePolyBAbstract {

    @Override
    public InfRuleID getID() {
        return InfRuleID.IDP_SMT_SPLIT;
    }

    @Override
    public String getLongName() {
        return "IDP_SMT_SPLIT simple: create all cases x >= 0, x < 0";
    }

    @Override
    public String getName() {
        return "IDP_SMT_SPLIT simple";
    }

    @Override
    protected GPolyVar decideNextSplit(
        Implication implication,
        GInterpretation<BigIntImmutable> interpretation,
        Map<GPolyVar, VarAnalysis> varAnalysis,
        Set<Set<MonomialAnalysis>> useableConstraints,
        Set<GPolyVar> remainingVariable)
    {
        for (VarAnalysis var : varAnalysis.values()) {
            if ((remainingVariable == null || remainingVariable.contains(var)) && var.getSign().getId() == null) {
                return var.getVar();
            }
        }
        return null;
    }

}
