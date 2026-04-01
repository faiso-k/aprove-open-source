package aprove.verification.oldframework.SMT.Solver.Z3;

import java.util.*;

import com.microsoft.z3.*;
import com.microsoft.z3.Model;

import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.Sort;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.Symbol;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;
import immutables.*;


public class Z3FunToFunctionDefinition {

    /**
     * @param name the name of the function we are interested in
     * @param interp A z3 function interpretation.
     * @param model The model in which interp lives.
     * @return A FunctionDefinition with a fresh function symbol which is equivalent to interp.
     */
    public static FunctionDefinition fromInterpretation(String name, FuncInterp interp, Model model) throws Z3Exception, SMTFeatureUnavailableException {
        if (interp.getNumEntries() > 0) {
            throw new SMTFeatureUnavailableException();
        }
        Z3ExpToSMTExpression transformer = new Z3ExpToSMTExpression(interp.getElse(), model);
        SMTExpression<? extends Sort> body = transformer.getRes();
        List<Symbol0<?>> args = transformer.getVars();
        com.microsoft.z3.Sort z3Sort = interp.getElse().getSort();
        if (!(z3Sort instanceof BoolSort) && !(z3Sort instanceof IntSort)) {
            throw new SMTFeatureUnavailableException();
        }
        Symbol<?> definedSymbol = Z3FunToFunctionDefinition.getFunctionSymbol(name, args, z3Sort);
        return new FunctionDefinition(definedSymbol, ImmutableCreator.create(new ArrayList<>(args)), body);
    }

    private static Symbol<?> getFunctionSymbol(String name, List<Symbol0<?>> args, com.microsoft.z3.Sort z3Sort) {
        return new Symbol<Sort>() {

            @Override
            public Sort[] getArgumentSorts() {
                final Sort[] argSorts = new Sort[args.size()];
                for (int i = 0; i < args.size(); i++) {
                    argSorts[i] = args.get(i).getReturnSort();
                }
                return argSorts;
            }

            @Override
            public Sort getReturnSort() {
                if (z3Sort instanceof BoolSort) {
                    return SBool.representative;
                } else if (z3Sort instanceof IntSort) {
                    return SInt.representative;
                } else {
                    throw new NotYetImplementedException();
                }
            }

            @Override
            public String toString() {
                return name;
            }

        };
    }

    public static FunctionDefinition fromConstant(Expr namedFunction, Model model) throws Z3Exception, SMTFeatureUnavailableException {
        Z3ExpToSMTExpression transformer = new Z3ExpToSMTExpression(namedFunction, model);
        SMTExpression<? extends Sort> body = transformer.getRes();
        List<Symbol0<?>> args = transformer.getVars();
        Symbol<?> definedSymbol = null;
        if (namedFunction.getSort() instanceof BoolSort) {
            definedSymbol = new NamedSymbol0<SBool>(SBool.representative, namedFunction.toString());
        } else if (namedFunction.getSort() instanceof IntSort) {
            definedSymbol = new NamedSymbol0<SInt>(SInt.representative, namedFunction.toString());
        } else {
            throw new SMTFeatureUnavailableException();
        }
        return new FunctionDefinition(definedSymbol, ImmutableCreator.create(new ArrayList<>(args)), body);
    }

}
