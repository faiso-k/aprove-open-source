package aprove.verification.oldframework.SMT.Solver.Z3;

import java.io.*;
import java.util.*;

import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.*;
import immutables.*;

public class Z3ExtSolver extends SMTLIBSolver implements Z3Solver {

    private static final SExpList GetModel = new SExpList(new SExpSymbol("get-model"));

    private static final SExpSymbol Model = new SExpSymbol("model");

    public Z3ExtSolver(SMTLIBLogic logic, SExpProcessCommunicator proc, boolean enable_unsat_core) {
        super(logic, proc, enable_unsat_core);
    }

    @Override
    public Optional<Model> getModel() {
        try {
            SExp result = this.proc.command(Z3ExtSolver.GetModel);
            return Optional.of(this.parseModel(result));
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        } catch (SMTFeatureUnavailableException e) {
            return Optional.empty();
        }
    }

    FunctionDefinition parseFunctionDefinition(SExp sExp) throws SMTFeatureUnavailableException {

        if (!(sExp instanceof SExpList)) {
            throw new SMTFeatureUnavailableException("could not parse function definition");
        }

        ImmutableList<SExp> args = ((SExpList) sExp).getArgs();

        if (args.size() != 5
            || !SMTLIBSymbols.defineFun.equals(args.get(0))
            || !(args.get(1) instanceof SExpSymbol)
            || !(args.get(2) instanceof SExpList)
            || !(args.get(3) instanceof SExpSymbol))
        {
            throw new SMTFeatureUnavailableException("could not parse function definition");
        }

        SExpSymbol name = (SExpSymbol) args.get(1);
        SExpList sortedvars = (SExpList) args.get(2);
        SExpSymbol returnSort = (SExpSymbol) args.get(3);

        SExp bodySExp = args.get(4);

        Symbol<?> definedSymbol = this.getSymbol(name);
        ArrayList<Symbol0<?>> arguments = new ArrayList<>();
        int argno = 0;
        Sort[] argumentSorts = definedSymbol.getArgumentSorts();
        LinkedHashMap<SExpSymbol, Symbol<?>> boundVariables = new LinkedHashMap<>();
        for (SExp arg : sortedvars.getArgs()) {
            if (!(arg instanceof SExpList)) {
                throw new SMTFeatureUnavailableException("could not parse function definition");
            }
            ImmutableList<SExp> argument = ((SExpList) arg).getArgs();
            if (argument.size() != 2 || !(args.get(0) instanceof SExpSymbol) || !(args.get(1) instanceof SExpSymbol)) {
                throw new SMTFeatureUnavailableException("could not parse function definition");
            }
            SExpSymbol a = (SExpSymbol) argument.get(0);
            Sort s = SMTLIBParserHelpers.parseSort(argument.get(1));
            Symbol0<?> v = s.createVariable();
            if (argno >= argumentSorts.length || !argumentSorts[argno].equals(s)) {
                throw new RuntimeException("Declaration of symbol does not match definition.");
            }
            boundVariables.put(a, v);
            arguments.add(v);
            ++argno;
        }
        ExpressionBuilderVisitor v = new ExpressionBuilderVisitor(boundVariables);
        SMTExpression<?> body = bodySExp.accept(v);

        if (!SMTLIBParserHelpers.parseSort(returnSort).equals(definedSymbol.getReturnSort())) {
            throw new RuntimeException("Declaration of symbol does not match definition.");
        }

        return new FunctionDefinition(definedSymbol, ImmutableCreator.create(arguments), body);
    }

    private Model parseModel(SExp model) throws SMTFeatureUnavailableException {
        LinkedHashMap<Symbol<?>, FunctionDefinition> definitions = new LinkedHashMap<>();

        if (!(model instanceof SExpList)) {
            throw new SMTFeatureUnavailableException("could not parse model");
        }

        ImmutableList<SExp> args = ((SExpList) model).getArgs();

        if (args.size() == 0 || !Z3ExtSolver.Model.equals(args.get(0))) {
            throw new SMTFeatureUnavailableException("could not parse model");
        }

        for (int i = 1, l = args.size(); i < l; ++i) {
            FunctionDefinition def = this.parseFunctionDefinition(args.get(i));
            Symbol<?> sym = def.getDefinedSymbol();
            definitions.put(sym, def);
        }
        return new Model(ImmutableCreator.create(definitions));
    }

    @Override
    public void reset() {
        throw new NotYetImplementedException();
    }
}
