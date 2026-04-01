/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.algorithms.orders;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.IDPGInterpretation.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class GPOLOINT extends GPOLONAT implements IActiveOrder {

    protected IDPGInterpretation idpInterpretation;

    /**
     * Create the order based on the given interpretation.
     * @param inter The interpretation.
     * @param orderPolyFactory a factory used to create order polynomials.
     * @param inner A FlatteningVisitor for inner polynomials.
     * @param outer A FlatteningVisitor for OrderPolys.
     */
    public GPOLOINT(IDPGInterpretation inter) {
        super(inter, inter.getFactory(), inter.getFvInner(), inter.getFvOuter());
        this.idpInterpretation = inter;
    }

    @Override
    protected boolean constraintFulfilled(
            final OrderPoly<BigIntImmutable> leftPoly, final OrderPoly<BigIntImmutable> rightPoly,
            final ConstraintType ct) {
        return true;
    }


    @Override
    public boolean orientsStrictly(GeneralizedRule rule) throws AbortionException {
        return this.solves(Constraint.<TRSTerm>create(rule.getLeft(), rule.getRight(), OrderRelation.GR));
    }

    @Override
    public Map<GeneralizedRule, Map<RelDependency, IDirection>> getOrientedUsables() {
        Map<GeneralizedRule, Map<RelDependency, IDirection>> res = new LinkedHashMap<GeneralizedRule, Map<RelDependency, IDirection>>();
        for (Map.Entry<GeneralizedRule, Map<ConstantType, Triple<OPCLogVar<BigIntImmutable>, Boolean, OrderPolyConstraint<BigIntImmutable>>>> entry : this.idpInterpretation.getLogVarRuleConstants().entrySet()) {
            GeneralizedRule rule = entry.getKey();
            Map<RelDependency, IDirection> orientations = new LinkedHashMap<RelDependency, IDirection>();
            for (ConstantType ct : ConstantType.values()) {
                if (ct.getCsar() == null) {
                    continue;
                }
                // System.err.println(ct + " "+ rule);
                if (this.idpInterpretation.getLogVarValue(ct, rule) != null && this.idpInterpretation.getLogVarValue(ct, rule)) {
                    IDirection dir = orientations.get(ct.getCsar());
                    if (dir != null) {
                        if (ct.getIncreasing()) {
                            switch (dir) {
                            case Reversed :
                                orientations.put(ct.getCsar(), IDirection.Both);
                                break;
                            case None :
                                orientations.put(ct.getCsar(), IDirection.Normal);
                                break;
                            }
                        } else {
                            switch (dir) {
                            case Normal :
                                orientations.put(ct.getCsar(), IDirection.Both);
                                break;
                            case None :
                                orientations.put(ct.getCsar(), IDirection.Reversed);
                                break;
                            }
                        }
                    } else {
                        if (ct.getIncreasing()) {
                            orientations.put(ct.getCsar(), IDirection.Normal);
                        } else {
                            orientations.put(ct.getCsar(), IDirection.Reversed);
                        }
                    }
                }
            }
            if (!orientations.isEmpty()) {
                res.put(rule, orientations);
            }
        }
        return res;
    }

}
