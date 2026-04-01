package aprove.verification.oldframework.SMT.Solver.Z3;

import java.util.*;
import java.util.Map.*;

import com.microsoft.z3.*;

import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.Symbol;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.Model;
import immutables.*;

public class Z3ModelToModel {

    private static int count = 0;
    private Map<Symbol<?>, FunctionDefinition> res = new LinkedHashMap<>();
    private com.microsoft.z3.Model model;
    private Map<Symbol<?>, AST> state;

    public Z3ModelToModel(com.microsoft.z3.Model model, Map<Symbol<?>, AST> state) {
        this.model = model;
        this.state = state;
    }

    public Optional<Model> transform() {
        try {
            this.transformState();
            return Optional.of(new Model(ImmutableCreator.create(this.res)));
        } catch (SMTFeatureUnavailableException | Z3Exception e) {
            return Optional.empty();
        }
    }

    private void transformState() throws SMTFeatureUnavailableException, Z3Exception {
        for (Entry<Symbol<?>, AST> e : this.state.entrySet()) {
            this.transform(e.getKey(), e.getValue());
        }
    }

    private void transform(Symbol<?> var, AST val) throws SMTFeatureUnavailableException, Z3Exception {
        if (val instanceof Expr) {
            Expr expr = this.model.getConstInterp((Expr) val);
            if (expr != null) {
                this.res.put(var, Z3FunToFunctionDefinition.fromConstant(expr, this.model));
            }
        } else if (val instanceof FuncDecl) {
            if (((FuncDecl) val).getArity() == 0) {
                Expr expr = this.model.getConstInterp((FuncDecl) val);
                if (expr != null) {
                    this.res.put(var, Z3FunToFunctionDefinition.fromConstant(expr, this.model));
                }
            } else {
                FuncInterp interp = this.model.getFuncInterp((FuncDecl) val);
                if (interp != null) {
                    String name;
                    if (var instanceof NamedSymbol<?>) {
                        name = ((NamedSymbol<?>) var).getName();
                    } else {
                        name ="fun" + count++;
                    }
                    FunctionDefinition def = Z3FunToFunctionDefinition.fromInterpretation(name, interp, this.model);
                    this.res.put(var, def);
                }
            }
        }
    }
}
