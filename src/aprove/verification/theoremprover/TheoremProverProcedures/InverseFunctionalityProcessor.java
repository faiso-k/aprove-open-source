package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

@NoParams
public class InverseFunctionalityProcessor extends TheoremProverProcessor {

    @Override
    protected Result process(TheoremProverObligation obligationInput,
            BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        // get formula
        Formula formula = obligationInput.getFormula();

        List<Equation> eqs = InverseFunctionalityProcessor.inverseFunctionality(formula);

        if (eqs==null || eqs.isEmpty()) {
            return ResultFactory.notApplicable();
        }

        Set<TheoremProverObligation> newObligations = new LinkedHashSet<TheoremProverObligation>();

        for (Equation equation : eqs) {
            newObligations.add(new TheoremProverObligation(equation, obligationInput));
        }

        return ResultFactory.provedAnd(newObligations, YNMImplication.SOUND,
                new InverseFunctionalityProof(newObligations));

    }

    public static List<Equation> inverseFunctionality(Formula formula) {

        if (!formula.isEquation()) {
            return null;
        }

        Equation equation = (Equation) formula;

        AlgebraTerm leftTerm = equation.getLeft();
        AlgebraTerm rightTerm = equation.getRight();

        if (!(leftTerm instanceof AlgebraFunctionApplication)
                || !(rightTerm instanceof AlgebraFunctionApplication)) {
            return null;
        }

        int size = equation.getLeft().getArguments().size();

        List<Equation> eqs = new ArrayList<Equation>(size);

        // check if the root symbols on both sides of the equation are equal
        if (leftTerm.getSymbol().equals(rightTerm.getSymbol())) {

            for (int index = 0; index < size; index++) {

                AlgebraTerm lArg = leftTerm.getArgument(index);
                AlgebraTerm rArg = rightTerm.getArgument(index);
                if (lArg.isVariable() || rArg.isVariable()) {
                    if (!lArg.equals(rArg)) {
                        // trivial equation, which we do not want to handle
                        return null;
                    }
                }

                if(!lArg.equals(rArg)){
                    Equation eq = Equation.create(lArg.deepcopy(), rArg.deepcopy());
                    eqs.add(eq);
                }

            }
        }

        return eqs;

    }

}
