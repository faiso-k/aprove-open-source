package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Syntax.*;

public class GetAllFunctionSymbolsVisitor implements CoarseFormulaVisitor<Set<DefFunctionSymbol>>,
        CoarseGrainedTermVisitor<Set<DefFunctionSymbol>> {

    protected Set<DefFunctionSymbol> functionSymbols;

    public static Set<DefFunctionSymbol> apply(Formula formula) {

        GetAllFunctionSymbolsVisitor getAllFunctionSymbolsVisitor = new GetAllFunctionSymbolsVisitor();
        return formula.apply(getAllFunctionSymbolsVisitor);
    }

    protected GetAllFunctionSymbolsVisitor() {
        super();
        this.functionSymbols = new LinkedHashSet<DefFunctionSymbol>();
    }

    @Override
    public Set<DefFunctionSymbol> caseTruthValue(FormulaTruthValue truthvalFormula) {
        return this.functionSymbols;
    }

    @Override
    public Set<DefFunctionSymbol> caseEquation(Equation eqFormula) {

        eqFormula.getLeft().apply(this);
        eqFormula.getRight().apply(this);

        return this.functionSymbols;
    }

    @Override
    public Set<DefFunctionSymbol> caseJunctorFormula(JunctorFormula jFormula) {

        jFormula.getLeft().apply(this);

        if(jFormula.getRight() != null) {
            jFormula.getRight().apply(this);
        }

        return this.functionSymbols;
    }

    @Override
    public Set<DefFunctionSymbol> caseVariable(AlgebraVariable v) {
        return this.functionSymbols;
    }

    @Override
    public Set<DefFunctionSymbol> caseFunctionApp(AlgebraFunctionApplication f) {

        for(AlgebraTerm argument : f.getArguments()) {
            argument.apply(this);
        }

        if(f.getFunctionSymbol() instanceof DefFunctionSymbol) {
            this.functionSymbols.add((DefFunctionSymbol)f.getFunctionSymbol().deepcopy());
        }

        return this.functionSymbols;
    }

}
