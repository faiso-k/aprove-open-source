package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;

public class EraseAnnotatedFormulaVisitor implements FineFormulaVisitor<Formula>, FineGrainedTermVisitor<AlgebraTerm> {

    public static Formula apply(Formula formula) {
        return formula.apply(new EraseAnnotatedFormulaVisitor());
    }

    public static AlgebraTerm apply(AlgebraTerm term) {
        return term.apply(new EraseAnnotatedFormulaVisitor());
    }

    public EraseAnnotatedFormulaVisitor() {
    }

    @Override
    public Formula caseAnd(And andFormula) {
        return And.create(andFormula.getLeft().apply(this), andFormula.getRight().apply(this));
    }

    @Override
    public Formula caseEquation(Equation phi) {
        return Equation.create(phi.getLeft().apply(this), phi.getRight().apply(this));
    }

    @Override
    public Formula caseEquivalence(Equivalence equivFormula) {
        return Equivalence.create(equivFormula.getLeft().apply(this), equivFormula.getRight().apply(this));
    }

    @Override
    public Formula caseImplication(Implication implFormula) {
        return Implication.create(implFormula.getLeft().apply(this), implFormula.getRight().apply(this));
    }

    @Override
    public Formula caseNot(Not notFormula) {
        return Not.create(notFormula.getLeft().apply(this));
    }

    @Override
    public Formula caseOr(Or orFormula) {
        return Or.create(orFormula.getLeft().apply(this), orFormula.getRight().apply(this));
    }

    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {
        return truthvalFormula.deepcopy();
    }

    @Override
    public AlgebraTerm caseConstructorApp(ConstructorApp cterm) {

        List<AlgebraTerm> newArguments = new Vector<AlgebraTerm>();

        for(AlgebraTerm argument : cterm.getArguments()) {
            newArguments.add(argument.apply(this));
        }

        return AlgebraFunctionApplication.create(cterm.getFunctionSymbol(), newArguments);

    }

    @Override
    public AlgebraTerm caseDefFunctionApp(DefFunctionApp fterm) {

        List<AlgebraTerm> newArguments = new Vector<AlgebraTerm>();

        for(AlgebraTerm argument : fterm.getArguments() ) {
            newArguments.add(argument.apply(this));
        }

        return AlgebraFunctionApplication.create(fterm.getFunctionSymbol(), newArguments);

    }

    @Override
    public AlgebraTerm caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {
        // MetaFunctionApplication have only one argument by definition
        return metaFunctionApplication.getArgument(0).apply(this);
    }

    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {
        return v.deepcopy();
    }

}
