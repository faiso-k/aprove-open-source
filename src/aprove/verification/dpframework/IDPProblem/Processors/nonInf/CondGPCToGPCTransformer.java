package aprove.verification.dpframework.IDPProblem.Processors.nonInf;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author mpluecke
 * @version $Id$
 */
public class CondGPCToGPCTransformer<C extends GPolyCoeff>  {

    public static enum SearchMode {
        FULL, P_LEQ_Q, P_EQ_Q, P_Q_ONE
    }


    public static final String Q_COEFF_PREFIX = "q_";
    public static final String P_COEFF_PREFIX = "p_";
    private static final OPCRange<BigIntImmutable> condRange = new OPCRange<BigIntImmutable>(BigIntImmutable.ZERO, BigIntImmutable.ONE);

    private int nextCoeff;
    private final OrderPolyFactory<C> factory;
    private final ConstraintFactory<C> constraintFactory;

    public CondGPCToGPCTransformer(OrderPolyFactory<C> factory, ConstraintFactory<C> constraintFactory) {
        this.nextCoeff = 1;
        this.factory = factory;
        this.constraintFactory = constraintFactory;
    }

    /**
     * We can transform
     *   p_1 >= q_1 /\ ... /\ p_n >= q_n  =>  r >= s
     * to
     *   P[r] - P[s]  >=  Q[p_1, ..., p_n] - Q[q_1, ..., q_n]
     * where P is an arbitrary  weakly  monotonic polynomial
     *   and Q is an arbitrary strictly monotonic polynomial.
     *
     * TODO generalize shape of these polynomials
     *
     * If the result of the transformation is satisfiable, then also the
     * original conditional constraint is.
     *
     * @param conds - conditions of the constraint
     * @param constraint - must hold if all of conds hold
     * @param ranges - is updated with information on the indefinite
     *  coefficients that are introduced for the conversion
     * @param sortConstraints - adds constraints that should hold (JUST FOR REDUCING SEARCH SPACE; MUST NOT CONTAIN ANY CORRECTNESS RELEVANT CONSTRAINTS);
     * @return a VPC whose satisfiability entails satisfiability of the
     *  corresponding conditional constraint with conds as conditions and
     *  constraint as constraint that must hold whenever all of conditions
     *  hold
     */
    public GPoly<GPoly<C, GPolyVar>, GPolyVar> transform(SearchMode mode, Collection<? extends GPoly<GPoly<C, GPolyVar>, GPolyVar>> conds, GPoly<GPoly<C, GPolyVar>, GPolyVar> constraint,
            Map<GPolyVar, OPCRange<BigIntImmutable>> ranges, Set<Pair<GPoly<C, GPolyVar>, ConstraintType>> sortConstraints) {

        // P[r] - P[s]  >=  Q[p_1, ..., p_n] - Q[q_1, ..., q_n]
        //   is equivalent to
        // P[r] - P[s] - Q[p_1, ..., p_n] + Q[q_1, ..., q_n]  >=  0.

        String pCoeff;
        GPoly<C, GPolyVar> pCoeffPoly;
        if (conds.size() > 1 && mode != SearchMode.P_Q_ONE && mode != SearchMode.P_EQ_Q) {
            pCoeff = this.getNextCoeff(CondGPCToGPCTransformer.P_COEFF_PREFIX);
            GPolyVar pCoeffVar = GAtomicVar.createVariable(pCoeff);
            pCoeffPoly = this.factory.getInnerFactory().plus(this.factory.getInnerFactory().one(), this.factory.getInnerFactory().buildFromVariable(pCoeffVar));
            ranges.put(pCoeffVar, new OPCRange<BigIntImmutable>(BigIntImmutable.ZERO, BigIntImmutable.create(BigInteger.valueOf(conds.size() - 1))));
         } else {
             pCoeffPoly = this.factory.getInnerFactory().one();
             // else just use 1 as coeffPoly, i.e., no coeff to search for at all
         }

        GPoly<GPoly<C, GPolyVar>, GPolyVar> current = this.factory.getFactory().times(constraint, this.factory.getFactory().buildFromCoeff(pCoeffPoly));
        List<GPoly<C, GPolyVar>> condCoeffs = new ArrayList<GPoly<C, GPolyVar>>(conds.size());
        for (GPoly<GPoly<C, GPolyVar>, GPolyVar> cond : conds) {
            String qCoeffName = this.getNextCoeff(CondGPCToGPCTransformer.Q_COEFF_PREFIX);
            GPolyVar qCoeffVar = GAtomicVar.createVariable(qCoeffName);
            ranges.put(qCoeffVar, CondGPCToGPCTransformer.condRange);
            GPoly<C, GPolyVar> qCoeff = this.factory.getInnerFactory().buildFromVariable(qCoeffVar);
            condCoeffs.add(qCoeff);
            current = this.factory.getFactory().minus(current, this.factory.getFactory().times(this.factory.buildFromCoeff(qCoeff), cond));
        }
        switch(mode) {
        case P_LEQ_Q:
            if (condCoeffs.size() != 1) {
                sortConstraints.add(new Pair<GPoly<C, GPolyVar>, ConstraintType>(
                        this.factory.getInnerFactory().plus(this.factory.getInnerFactory().minus(this.factory.getInnerFactory().plus(condCoeffs), pCoeffPoly), this.factory.getInnerFactory().one()),
                        ConstraintType.GE)
                );
            }
            break;
        case P_EQ_Q:
            if (!condCoeffs.isEmpty()) {
                sortConstraints.add(new Pair<GPoly<C, GPolyVar>, ConstraintType>(
                            this.factory.getInnerFactory().minus(this.factory.getInnerFactory().plus(condCoeffs), pCoeffPoly),
                            ConstraintType.EQ)
                );
            }
            break;
        case P_Q_ONE:
            sortConstraints.add(new Pair<GPoly<C, GPolyVar>, ConstraintType>(
                    this.factory.getInnerFactory().minus(this.factory.getInnerFactory().plus(condCoeffs), this.factory.getInnerFactory().one()),
                    ConstraintType.EQ)
            );
            break;

        }
        return this.factory.wrap(current);
    }

    private String getNextCoeff(String prefix) {
        return prefix+(this.nextCoeff++);
    }
}
