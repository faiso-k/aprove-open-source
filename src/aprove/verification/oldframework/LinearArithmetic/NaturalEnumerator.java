package aprove.verification.oldframework.LinearArithmetic;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Transformer of LinearIntegerConstraints x <= c into
 * the dissolving x=0 or x=1 or ... or x=c
 * Works only for natural numbers
 *
 * @author dickmeis
 * @version $Id$
 */

public class NaturalEnumerator {

    /**
     * When there is a constraint of the form x<=c
     * it gets split up into several dissolvings x=0 or x=1 or ... or x=c
     * each in a new context.
     * The disjunction of the output is equivalent to the input.
     *
     * @param constraints The initial constraints.
     * @param dissolvings The initial dissolvings
     * @param variableOrdering  A list of pairs of transformed contraints and dissolvings
     * @return
     */
    public static List<Pair<List<LinearConstraint>, List<Dissolving>>> enumerate(
            List<LinearConstraint> constraints, List<Dissolving> dissolvings,
            List<AlgebraVariable> variableOrdering) {
        List<Pair<List<LinearConstraint>, List<Dissolving>>> enumerated =
            new ArrayList<Pair<List<LinearConstraint>, List<Dissolving>>>(1);
        Pair<List<LinearConstraint>, List<Dissolving>> p =
            new Pair<List<LinearConstraint>, List<Dissolving>>(constraints, dissolvings);
        enumerated.add(p);

        int count = enumerated.size();

        boolean done;
        do {
            done = false;

            for (int k = 0; k < count; k++) {
                Pair<List<LinearConstraint>, List<Dissolving>> pair = enumerated
                        .get(k);
                List<LinearConstraint> p_constraints = pair.x;

                int size = p_constraints.size();
                for (int s = 0; s < size; s++) {
                    LinearConstraint constraint = p_constraints.get(s);

                    ConstraintType ct = constraint.getConstraintType();
                    if (ct.equals(ConstraintType.LESSEQ)) {
                        Set<AlgebraVariable> vars = constraint.getUsedVariables();

                        Rational r = constraint.getConstant();
                        // we deal only with natural numbers here
                        int c = r.getNumerator();

                        if (vars.size() == 1  && c > 0) {
                            // found something to enumerate

                            List<Dissolving> p_dissolvings = pair.y;



                            List<Pair<List<LinearConstraint>, List<Dissolving>>> newPairs = new ArrayList<Pair<List<LinearConstraint>, List<Dissolving>>>(
                                    c);

                            for (int i = 0; i <= c; i++) {
                                ArrayList<LinearConstraint> newConstraints = new ArrayList<LinearConstraint>(
                                        p_constraints.size());
                                for (int t = 0; t < size; t++) {
                                    if (t != s) {
                                        LinearConstraint constr = p_constraints
                                                .get(t);
                                        constr = constr.deepcopy();
                                        newConstraints.add(constr);
                                    }
                                }
                                Map<AlgebraVariable, Rational> coeffs = constraint
                                        .getCoefficients();
                                LinearConstraint eq = new LinearConstraint(
                                        coeffs, ConstraintType.EQUALITY,
                                        new Rational(i));
                                newConstraints.add(eq);

                                LASolver las = new LASolver(variableOrdering);
                                las.addAllConstraints(newConstraints);

                                for (Dissolving dissolving : p_dissolvings) {
                                    eq = dissolving.toEquation();
                                    las.addConstraint(eq);
                                }

                                boolean solvable = las.solve();

                                if (solvable) {
                                    newConstraints = las.getAllConstraints();
                                    ArrayList<Dissolving> newDissolvings = las
                                            .getDissolvings();

                                    Pair<List<LinearConstraint>, List<Dissolving>> newp =
                                        new Pair<List<LinearConstraint>, List<Dissolving>>(
                                            newConstraints, newDissolvings);

                                    newPairs.add(newp);
                                }
                            }

                            enumerated.remove(pair);
                            enumerated.addAll(newPairs);
                            count = count - 1 + newPairs.size();
                            k--;
                            done = true;
                        }
                    }

                }
            }
        }
        while (done);

        return enumerated;
    }
}
