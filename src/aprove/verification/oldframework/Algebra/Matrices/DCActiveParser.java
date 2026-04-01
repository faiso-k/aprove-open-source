package aprove.verification.oldframework.Algebra.Matrices;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Algebra.Matrices.Interpretation.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Converts SimplePolyConstraints and QActiveConditions to diophantine Constraints.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class DCActiveParser {

    public static final String ACTIVE = "active";


    public static Pair<Set<SimplePolyConstraint>, ActiveResolver> convert( Map<QActiveCondition,Set<SimplePolyConstraint>> input, MatrixFactory fact, ArgumentInterpretor argInter, Abortion aborter) throws AbortionException {

        ActiveResolver activeResolver;

        activeResolver = new ActiveResolver();
        activeResolver.setIsActive();
        int vc = 0;


        Set<SimplePolyConstraint> constraints = new LinkedHashSet<SimplePolyConstraint>();

        for (Map.Entry<QActiveCondition, Set<SimplePolyConstraint>> entry: input.entrySet()) {
            SimplePolynomial activeCond = SimplePolynomial.create(DCActiveParser.ACTIVE + Integer.toString(vc++));
            DCActiveParser.addActiveConstraints(constraints, entry.getKey(), activeCond, aborter, argInter, fact);

            activeResolver.put(entry.getKey(), activeCond);


            for (SimplePolyConstraint spc: entry.getValue()) {
                constraints.add (new SimplePolyConstraint( spc.getPolynomial().times(activeCond), spc.getType()));
            }
        }


        return new Pair<Set<SimplePolyConstraint>, ActiveResolver>(constraints, activeResolver);

    }


    public static void addActiveConstraints(Set<SimplePolyConstraint> constraints, QActiveCondition condition, SimplePolynomial activeCondition, Abortion aborter, ArgumentInterpretor argInter, MatrixFactory fact) throws AbortionException {
        activeCondition = activeCondition.plus(SimplePolynomial.MINUS_ONE);
        for (Set<Pair<FunctionSymbol, Integer>> andCondition : condition.getSetRepresentation()) {
            aborter.checkAbortion();
            SimplePolynomial product = SimplePolynomial.ONE;
            for (Pair<FunctionSymbol, Integer> pair : andCondition) {

                List<SimplePolynomial> coeffPoly = argInter.getFSymCoefficients(pair.x, pair.y, fact) ;
                product = product.times(SimplePolynomial.plus(coeffPoly));

            }

            if (product.getNumericalAddend().compareTo(BigInteger.ZERO) > 0) {
                constraints.add(new SimplePolyConstraint(activeCondition, ConstraintType.EQ));
                return;
            } else {
                constraints.add(new SimplePolyConstraint(activeCondition.times(product), ConstraintType.EQ));
            }
        }
    }


}

