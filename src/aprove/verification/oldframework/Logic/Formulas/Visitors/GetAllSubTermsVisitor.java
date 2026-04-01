package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;

public class GetAllSubTermsVisitor implements CoarseFormulaVisitor<Set<AlgebraTerm>> {

    protected Set<AlgebraTerm> subTerms;

    public static Set<AlgebraTerm> apply(Formula formula) {
        return formula.apply(new GetAllSubTermsVisitor());
    }

    protected GetAllSubTermsVisitor() {
        this.subTerms = new LinkedHashSet<AlgebraTerm>();
    }

    @Override
    public Set<AlgebraTerm> caseTruthValue(FormulaTruthValue truthvalFormula) {
        return this.subTerms;
    }

    @Override
    public Set<AlgebraTerm> caseEquation(Equation eqFormula) {

        this.subTerms.addAll(eqFormula.getLeft().getAllSubterms());
        this.subTerms.addAll(eqFormula.getRight().getAllSubterms());

        return this.subTerms;
    }

    @Override
    public Set<AlgebraTerm> caseJunctorFormula(JunctorFormula jFormula) {

        jFormula.getLeft().apply(this);

        if(jFormula.getRight() != null ) {
            jFormula.getRight().apply(this);
        }

        return this.subTerms;
    }

}
