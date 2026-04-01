package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;
import aprove.verification.oldframework.Logic.Formulas.*;

public class GetRepresentationStringVisitor implements CoarseGrainedTermVisitor<List<IndexSymbol>>, FineFormulaVisitor<List<IndexSymbol>> {

    protected List<IndexSymbol> representationIndexSymbol;

    public static List<IndexSymbol> apply(Formula formula) {
        GetRepresentationStringVisitor getRepresentationStringVisitor = new GetRepresentationStringVisitor();
        return formula.apply(getRepresentationStringVisitor);
    }

    public static List<IndexSymbol> apply(AlgebraTerm term) {
        GetRepresentationStringVisitor getRepresentationStringVisitor = new GetRepresentationStringVisitor();
        return term.apply(getRepresentationStringVisitor);
    }

    public GetRepresentationStringVisitor() {
        this.representationIndexSymbol = new Vector<IndexSymbol>();
    }

    @Override
    public List<IndexSymbol> caseVariable(AlgebraVariable v) {
        this.representationIndexSymbol.add(new IndexVariableSymbol());
        return this.representationIndexSymbol;
    }

    @Override
    public List<IndexSymbol> caseFunctionApp(AlgebraFunctionApplication f) {
        this.representationIndexSymbol.add(new IndexFunctionSymbol(f.getSymbol().getName()));
        for(AlgebraTerm argument : f.getArguments()) {
            argument.apply(this);
        }
        return this.representationIndexSymbol;
    }

    @Override
    public List<IndexSymbol> caseTruthValue(FormulaTruthValue truthvalFormula) {
        this.representationIndexSymbol.add(new IndexTruthValueSymbol(truthvalFormula.getValue()));
        return this.representationIndexSymbol;
    }

    @Override
    public List<IndexSymbol> caseEquation(Equation phi) {
        this.representationIndexSymbol.add(new IndexEquationSymbol());
        phi.getLeft().apply(this);
        phi.getRight().apply(this);
        return this.representationIndexSymbol;
    }

    @Override
    public List<IndexSymbol> caseNot(Not notFormula) {
        this.representationIndexSymbol.add(new IndexNotSymbol());
        notFormula.getLeft().apply(this);
        return this.representationIndexSymbol;
    }

    @Override
    public List<IndexSymbol> caseAnd(And andFormula) {
        this.representationIndexSymbol.add(new IndexAndSymbol());
        andFormula.getLeft().apply(this);
        andFormula.getRight().apply(this);
        return this.representationIndexSymbol;
    }

    @Override
    public List<IndexSymbol> caseOr(Or orFormula) {
        this.representationIndexSymbol.add(new IndexOrSymbol());
        orFormula.getLeft().apply(this);
        orFormula.getRight().apply(this);
        return this.representationIndexSymbol;
    }

    @Override
    public List<IndexSymbol> caseImplication(Implication implFormula) {
        this.representationIndexSymbol.add(new IndexImplicationSymbol());
        implFormula.getLeft().apply(this);
        implFormula.getRight().apply(this);
        return this.representationIndexSymbol;
    }

    @Override
    public List<IndexSymbol> caseEquivalence(Equivalence equivFormula) {
        this.representationIndexSymbol.add(new IndexEquivalenceSymbol());
        equivFormula.getLeft().apply(this);
        equivFormula.getRight().apply(this);
        return this.representationIndexSymbol;
    }

}
