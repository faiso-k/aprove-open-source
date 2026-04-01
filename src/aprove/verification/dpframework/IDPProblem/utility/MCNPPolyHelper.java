package aprove.verification.dpframework.IDPProblem.utility;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.Processors.IDPMCNPProcessor.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Provides some auxiliary methods for Itpfs to help in getting from IDP
 * problems "as close as possible" to Monotonicity Constraints,
 * which we can then export for further processing.
 *
 * @author Carsten Fuhs
 */
public class MCNPPolyHelper {

    private final IDPGInterpretation interpretation;
    private final OrderPolyFactory<BigIntImmutable> factory;

    private MCNPPolyHelper(IDPGInterpretation interpretation) {
        this.interpretation = interpretation;
        this.factory = interpretation.getFactory();
    }

    /**
     * @param predefinedMap
     * @return an MCNPPolyHelper for the provided interpretation
     */
    public static MCNPPolyHelper create(IDPGInterpretation interpretation) {
        return new MCNPPolyHelper(interpretation);
    }


    /**
     * @param argInter - [p_1, ..., p_n]
     * @param nameGen - makes fresh var_i
     * @return [var_1 = p_1, ..., var_n = p_n]
     */
    public List<Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>> zipWithFreshVars(
            List<OrderPoly<BigIntImmutable>> argInter, MCNPNameGenerator nameGen,
            Abortion aborter) throws AbortionException {
        List<Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>> res =
            new ArrayList<Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>>(argInter.size());
        for (OrderPoly<BigIntImmutable> poly : argInter) {
            OrderPoly<BigIntImmutable> freshVar = nameGen.getNextPolyVariable(this.interpretation, aborter);
            res.add(new Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>(freshVar, Relation.EQ, poly));
        }
        return res;
    }

    // code for converting constants to program point arguments

    public void collectNaturalOrderConstraints(SortedMap<BigIntImmutable, Pair<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>>> numToVars, boolean left,
                    List<Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>> constraints) {
        OrderPoly<BigIntImmutable> smaller;
        OrderPoly<BigIntImmutable> greater = null;
        for (Pair<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>> lr : numToVars.values()) {
            smaller = greater;
            greater = left ? lr.x : lr.y;
            if (smaller != null) {
                constraints.add(new Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>(greater, Relation.GT, smaller));
            }
        }
    }

    public void collectLeqRConstraints(SortedMap<BigIntImmutable, Pair<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>>> numToVars,
            List<Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>> constraints) {
        for (Pair<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>> lr : numToVars.values()) {
            constraints.add(new Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>(lr.x, Relation.EQ, lr.y));
        }
    }

    public OrderPoly<BigIntImmutable> replaceConstantByVar(OrderPoly<BigIntImmutable> poly, boolean left,
            SortedMap<BigIntImmutable, Pair<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>>> numToVars) {
        OrderPoly<BigIntImmutable> constantPoly = this.getConstantPart(poly);
        BigIntImmutable constantValue = this.getConstantValue(poly);

        Pair<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>> lrVar = numToVars.get(constantValue);
        OrderPoly<BigIntImmutable> var = left ? lrVar.x : lrVar.y;
        OrderPoly<BigIntImmutable> res = this.factory.plus( this.factory.minus(poly, constantPoly), var);
        return res;
    }


    private BigIntImmutable getConstantValue(OrderPoly<BigIntImmutable> poly) {
        GPoly<BigIntImmutable, GPolyVar> constantAddend = poly.getConstantPart(this.interpretation.getOuterRingMonoid());
        BigIntImmutable res = constantAddend.getConstantPart(this.interpretation.getInnerRingMonoid());
        return res;
    }


    private OrderPoly<BigIntImmutable> getConstantPart(OrderPoly<BigIntImmutable> poly) {
        GPoly<BigIntImmutable, GPolyVar> constantAddend = poly.getConstantPart(this.interpretation.getOuterRingMonoid());
        OrderPoly<BigIntImmutable> res = this.factory.buildFromCoeff(constantAddend);
        return res;
    }

    public Pair<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>>
            getLRvarsForNumber(BigIntImmutable number,
                        SortedMap<BigIntImmutable, Pair<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>>> numToVars,
                        MCNPNameGenerator nameGen, Abortion aborter)
                            throws AbortionException {
        Pair<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>> res = numToVars.get(number);
        if (res == null) {
            OrderPoly<BigIntImmutable> leftPoly = nameGen.getNextPolyVariable(this.interpretation, aborter);
            OrderPoly<BigIntImmutable> rightPoly = nameGen.getNextPolyVariable(this.interpretation, aborter);
            res = new Pair<OrderPoly<BigIntImmutable>, OrderPoly<BigIntImmutable>>(leftPoly, rightPoly);
            numToVars.put(number, res);
        }
        return res;
    }

}
