package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Syntax.*;

public class GetAllVariableSymbolsVisitor implements CoarseFormulaVisitor<Set<VariableSymbol>> {

    protected Set<VariableSymbol> variableSymbols;

    public static Set<VariableSymbol> apply(Formula formula) {
        return formula.apply(new GetAllVariableSymbolsVisitor());
    }

    private GetAllVariableSymbolsVisitor() {
        this.variableSymbols = new LinkedHashSet<VariableSymbol>();
    }

    @Override
    public Set<VariableSymbol> caseEquation(Equation eqFormula) {
        this.variableSymbols.addAll(eqFormula.getLeft().getVariableSymbols());
        this.variableSymbols.addAll(eqFormula.getRight().getVariableSymbols());
        return this.variableSymbols;
    }

    @Override
    public Set<VariableSymbol> caseJunctorFormula(JunctorFormula jFormula) {
        jFormula.getLeft().apply(this);
        if(jFormula.getRight()!=null) {
            jFormula.getRight().apply(this);
        }
        return this.variableSymbols;
    }

    @Override
    public Set<VariableSymbol> caseTruthValue(FormulaTruthValue truthvalFormula) {
        return this.variableSymbols;
    }


}
