package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Implements the conversion from conditional VarPolyConstraints to
 * unconditional (and hence perfectly ordinary) VarPolyConstraints
 * as described in the RTA'08 paper by Fuhs, Giesl, Middeldorp,
 * Schneider-Kamp, Thiemann, and Zankl.
 *
 * @author fuhs
 * @version $Id$
 */
public class CondVPCToVPCTransformer {

    private static final String COEFF_PREFIX = "d_";
    private int nextCoeff;

    public CondVPCToVPCTransformer() {
        this.nextCoeff = 1;
    }

    /**
     * We can transform
     *   p_1 >= q_1 /\ ... /\ p_n >= q_n  =>  r >= s
     * to
     *   Q[r] - Q[s]  >=  P[p_1, ..., p_n] - P[q_1, ..., q_n]
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
     * @return a VPC whose satisfiability entails satisfiability of the
     *  corresponding conditional constraint with conds as conditions and
     *  constraint as constraint that must hold whenever all of conditions
     *  hold
     */
    private VarPolyConstraint transform(Collection<VarPolyConstraint> conds, VarPolyConstraint constraint,
            Map<String, BigInteger> ranges) {
        // A general approach could use special shapes of P and Q as
        // parameters, e.g., for the constructor.

        // For now, hard-code the shapes of P and Q:
        //   P: d_1 * x_1 + ... + d_n * x_n where d_i over {0, 1}
        //   Q:   e * x_1 where e over {1, ..., d_1+...+d_n}
        /*
        SimplePolynomial[] pCoeffPoly = new SimplePolynomial[conds.size()];
        for (int i = 0; i < pCoeffPoly.length; ++i) {
            String pCoeff = this.getNextCoeff();
            pCoeffPoly[i] = SimplePolynomial.create(pCoeff);
            ranges.put(pCoeff, 1);
        }

        String qCoeff;
        SimplePolynomial qCoeffPoly = SimplePolynomial.ONE;
        if (conds.size() > 1) {
            qCoeff = this.getNextCoeff();
            qCoeffPoly = qCoeffPoly.plus(SimplePolynomial.create(qCoeff));
            ranges.put(qCoeff, conds.size() - 1);
        } // else just use 1 as coeffPoly, i.e., no coeff to search for at all
*/
        // Q[r] - Q[s]  >=  P[p_1, ..., p_n] - P[q_1, ..., q_n]
        //   is equivalent to
        // Q[r] - Q[s] - P[p_1, ..., p_n] + P[q_1, ..., q_n]  >=  0.

        if (Globals.useAssertions) {
            assert constraint.getType() == ConstraintType.GE;
            for (VarPolyConstraint vpc : conds) {
                assert vpc.getType() == ConstraintType.GE;
            }
        }

        List<VarPolynomial> addends = new ArrayList<VarPolynomial>(2*conds.size()+2);

        if (true) { // with the abstract coeffs
            String qCoeff;
            SimplePolynomial qCoeffPoly = SimplePolynomial.ONE; // for strict monotonicity
            if (conds.size() > 1) {
                qCoeff = this.getNextCoeff();
                qCoeffPoly = qCoeffPoly.plus(SimplePolynomial.create(qCoeff));
                ranges.put(qCoeff, BigInteger.valueOf(conds.size() - 1));
            } // else just use 1 as coeffPoly, i.e., no coeff to search for at all

            VarPolynomial current = constraint.getPolynomial().times(qCoeffPoly);
            addends.add(current);

            SimplePolynomial[] pCoeffPoly = new SimplePolynomial[conds.size()];
            for (int i = 0; i < pCoeffPoly.length; ++i) {
                String pCoeff = this.getNextCoeff();
                pCoeffPoly[i] = SimplePolynomial.create(pCoeff);
                ranges.put(pCoeff, BigInteger.ONE);
            }
            int pIndex = 0;
            for (VarPolyConstraint vpCond : conds) {
                current = vpCond.getPolynomial().times(pCoeffPoly[pIndex].negate());
                addends.add(current);
                ++pIndex;
            }
        }
        else { // w/o abstract coeffs (assume maximum values of the heuristics
               // for them)
            ////VarPolynomial current = constraint.getLhs().times(qCoeffPoly);
            VarPolynomial current = constraint.getPolynomial().times(SimplePolynomial.create(conds.size()+1));

            addends.add(current);
            ////current = constraint.getRhs().times(qCoeffPoly.negate());
            int pIndex = 0;
            for (VarPolyConstraint vpCond : conds) {
                ////current = vpCond.getLhs().times(pCoeffPoly[pIndex].negate());
                current = vpCond.getPolynomial().negate();
                addends.add(current);
                ////current = vpCond.getRhs().times(pCoeffPoly[pIndex]);
                ++pIndex;
            }
        }
        VarPolynomial resultingPoly = VarPolynomial.plus(addends);
        VarPolyConstraint result = new VarPolyConstraint(resultingPoly,
                ConstraintType.GE);
        return result;
    }


    /**
     * Convenience method.
     *
     * @param condVPCs
     * @param ranges
     * @return
     */
    public Set<VarPolyConstraint> transform(Collection<CondVPC> condVPCs,
            Map<String, BigInteger> ranges) {
        // first flatten the constraints ...
        Set<Pair<? extends Collection<VarPolyConstraint>, VarPolyConstraint>> flatCondVPCs;
        flatCondVPCs = new LinkedHashSet<Pair<? extends Collection<VarPolyConstraint>, VarPolyConstraint>>(condVPCs.size());
        for (CondVPC condVPC : condVPCs) {
            Pair<? extends Collection<VarPolyConstraint>, VarPolyConstraint> flatCondVPC;
            flatCondVPC = condVPC.getFlattened();
            flatCondVPCs.add(flatCondVPC);
        }

        // ... then transform them
        Set<VarPolyConstraint> result = this.transformFlattened(flatCondVPCs, ranges);
        return result;
    }


    /**
     * Convenience method.
     *
     * @param flatCondVPCs
     * @param ranges  - info on the ranges for the fresh coeffs is stored here
     * @return
     */
    private Set<VarPolyConstraint> transformFlattened(Collection<Pair<? extends Collection<VarPolyConstraint>, VarPolyConstraint>> flatCondVPCs,
            Map<String, BigInteger> ranges) {
        Set<VarPolyConstraint> result = new LinkedHashSet<VarPolyConstraint>(flatCondVPCs.size());
        for (Pair<? extends Collection<VarPolyConstraint>, VarPolyConstraint> condVPC : flatCondVPCs) {
            Collection<VarPolyConstraint> premises = condVPC.getKey();
            VarPolyConstraint conclusion = condVPC.getValue();
            VarPolyConstraint currentVPC = this.transform(premises, conclusion, ranges);
            result.add(currentVPC);
        }
        return result;
    }



    /**
     * Transform a conditional constraint to an unconditional one, introducing
     * fresh indefinite coefficients in the process.
     *
     * @param condVPC
     * @param ranges - info on the ranges for the fresh coeffs is stored here
     * @return
     */
    public VarPolyConstraint transform(CondVPC condVPC,
            Map<String, BigInteger> ranges) {
        Pair<Set<VarPolyConstraint>, VarPolyConstraint> flattenedCondVPC;
        flattenedCondVPC = condVPC.getFlattened();
        VarPolyConstraint result = this.transform(flattenedCondVPC.x,
                flattenedCondVPC.y, ranges);
        return result;
    }


    private String getNextCoeff() {
        return CondVPCToVPCTransformer.COEFF_PREFIX+(this.nextCoeff++);
    }
}
