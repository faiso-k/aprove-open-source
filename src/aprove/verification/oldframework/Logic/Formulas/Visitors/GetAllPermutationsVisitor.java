package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Logic.Formulas.*;

public class GetAllPermutationsVisitor implements FineFormulaVisitor<Set<Formula>> {

    public static Set<Formula> apply(Formula formula) {
        return formula.apply(new GetAllPermutationsVisitor());
    }

    protected GetAllPermutationsVisitor() {
    }

    @Override
    public Set<Formula> caseAnd(And andFormula) {
        Set<Formula> returnValue = new LinkedHashSet<Formula>();

        Set<Formula> leftPermutations  = andFormula.getLeft().apply(this);
        Set<Formula> rightPermutations = andFormula.getRight().apply(this);

        for (Formula leftPermutation : leftPermutations) {
            for (Formula rightPermutation : rightPermutations) {
                returnValue.add(And.create(leftPermutation.deepcopy(),
                        rightPermutation.deepcopy()));
            }
        }

        for (Formula leftPermutation : rightPermutations) {
            for (Formula rightPermutation : leftPermutations) {
                returnValue.add(And.create(leftPermutation.deepcopy(),
                        rightPermutation.deepcopy()));
            }
        }

        return returnValue;
    }

    @Override
    public Set<Formula> caseEquation(Equation phi) {
        Set<Formula> returnValue = new LinkedHashSet<Formula>();
        returnValue.add(phi.deepcopy());
        returnValue.add(Equation.create(phi.getRight().deepcopy(),phi.getLeft().deepcopy()));
        return returnValue;
    }

    @Override
    public Set<Formula> caseEquivalence(Equivalence equivFormula) {
        Set<Formula> returnValue = new LinkedHashSet<Formula>();

        Set<Formula> leftPermutations = equivFormula.getLeft().apply(this);
        Set<Formula> rightPermutations = equivFormula.getRight().apply(this);

        for (Formula leftPermutation : leftPermutations) {
            for (Formula rightPermutation : rightPermutations) {
                returnValue.add(Equivalence.create(leftPermutation.deepcopy(),
                        rightPermutation.deepcopy()));
            }
        }

        return returnValue;

    }

    @Override
    public Set<Formula> caseImplication(Implication implFormula) {
        Set<Formula> returnValue = new LinkedHashSet<Formula>();

        Set<Formula> leftPermutations  = implFormula.getLeft().apply(this);
        Set<Formula> rightPermutations = implFormula.getRight().apply(this);

        for(Formula leftPermutation : leftPermutations) {
            for(Formula rightPermutation : rightPermutations) {
                returnValue.add(Implication.create(leftPermutation.deepcopy(),
                        rightPermutation.deepcopy()));
            }
        }

        return returnValue;
    }

    @Override
    public Set<Formula> caseNot(Not notFormula) {
        Set<Formula> returnValue = new LinkedHashSet<Formula>();

        Set<Formula> leftPermutations  = notFormula.getLeft().apply(this);
        for(Formula leftPermutation : leftPermutations) {
            returnValue.add(Not.create(leftPermutation.deepcopy()));
        }
        return returnValue;
    }

    @Override
    public Set<Formula> caseOr(Or orFormula) {
        Set<Formula> returnValue = new LinkedHashSet<Formula>();

        Set<Formula> leftPermutations  = orFormula.getLeft().apply(this);
        Set<Formula> rightPermutations = orFormula.getRight().apply(this);

        for (Formula leftPermutation : leftPermutations) {
            for (Formula rightPermutation : rightPermutations) {
                returnValue.add(Or.create(leftPermutation.deepcopy(),
                        rightPermutation.deepcopy()));
            }
        }

        for (Formula leftPermutation : rightPermutations) {
            for (Formula rightPermutation : leftPermutations) {
                returnValue.add(Or.create(leftPermutation.deepcopy(),
                        rightPermutation.deepcopy()));
            }
        }

        return returnValue;
    }

    @Override
    public Set<Formula> caseTruthValue(FormulaTruthValue truthvalFormula) {
        Set<Formula> returnValue = new LinkedHashSet<Formula>();
        returnValue.add(truthvalFormula.deepcopy());
        return returnValue;
    }

}
