package aprove.verification.oldframework.SMT.Solver.SMTLIB;

import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.*;
import immutables.*;

public class ToStringVisitor extends BuildSExpVisitor {

    private int varcount = 0;
    private final LinkedHashMap<Symbol<?>, SExpSymbol> names = new LinkedHashMap<>();

    private ToStringVisitor() {
        super(null, false);
    }

    @Override
    public SExp getDeclaredAtom(Symbol<?> sym) {
        if (!this.names.containsKey(sym)) {
            this.names.put(sym, new SExpSymbol("x" + this.varcount++));
        }
        return this.names.get(sym);
    }

    public static String convertExpressionToString(SMTExpression<?> e) {
        ToStringVisitor v = new ToStringVisitor();
        SExp s = e.accept(v);
        return s.toString();
    }

    @Override
    public <S extends Sort> SExp visit(Exists<S> exists) {
        ArrayList<SExp> varDecls = new ArrayList<>();
        SExp body = exists.getBody().accept(this);
        for (Symbol0<?> v : exists.getVars()) {
            ArrayList<SExp> decl = new ArrayList<>(2);
            if (v instanceof NamedSymbol0<?>) {
                String name = ((NamedSymbol0<?>) v).getName();
                decl.add(new SExpSymbol((name.startsWith("s")) ? "_" + name : name));
            } else {
                decl.add(this.getDeclaredAtom(v));
            }
            decl.add(new SExpSymbol(v.getType().toString()));
            varDecls.add(new SExpList(ImmutableCreator.create(decl)));
        }
        return new SExpList(SMTLIBSymbols.Exists, new SExpList(ImmutableCreator.create(varDecls)), body);
    }

    @Override
    public <S extends Sort> SExp visit(Forall<S> forall) {
        ArrayList<SExp> varDecls = new ArrayList<>();
        SExp body = forall.getBody().accept(this);
        for (Symbol0<?> v : forall.getVars()) {
            ArrayList<SExp> decl = new ArrayList<>(2);
            if (v instanceof NamedSymbol0<?>) {
                String name = ((NamedSymbol0<?>) v).getName();
                decl.add(0, new SExpSymbol((name.startsWith("s")) ? "_" + name : name));
            } else {
                decl.add(0, this.getDeclaredAtom(v));
            }
            decl.add(1, new SExpSymbol(v.getType().toString()));
            varDecls.add(new SExpList(ImmutableCreator.create(decl)));
        }
        return new SExpList(SMTLIBSymbols.Forall, new SExpList(ImmutableCreator.create(varDecls)), body);
    }


    @Override
    public <S extends Sort> SExp visit(Symbol0<S> symbol0) {
        if (symbol0 instanceof NamedSymbol0<?>) {
            String name = ((NamedSymbol0<?>) symbol0).getName();
            return new SExpSymbol((name.startsWith("s")) ? "_" + name : name);
        } else {
            return super.visit(symbol0);
        }
    }
}
