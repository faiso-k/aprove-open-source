package aprove.verification.oldframework.SMT.Solver.SMTLIB;

import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.*;

public class ExpressionBuilderVisitor implements SExpVisitor<SMTExpression<?>> {

    // TODO use this to handle local variables properly
    @SuppressWarnings("unused")
    private LinkedHashMap<SExpSymbol, Symbol<?>> boundVariables;

    public ExpressionBuilderVisitor(LinkedHashMap<SExpSymbol, Symbol<?>> boundVariables) {
        this.boundVariables = boundVariables;
    }

    @Override
    public SMTExpression<?> visit(SExpBinary sExpBinary) {
        throw new RuntimeException("not implemented");
    }

    @Override
    public SMTExpression<?> visit(SExpDecimal sExpDecimal) {
        throw new RuntimeException("not implemented");
    }

    @Override
    public SMTExpression<?> visit(SExpKeyword sExpKeyword) {
        throw new RuntimeException("not implemented");
    }

    @Override
    public SMTExpression<?> visit(SExpList sExpList) {
        // this is a function application
        SExp function = sExpList.get(0);
        if (!(function instanceof SExpSymbol)) {
            throw new UnsupportedOperationException("not implemented");
        }
        SExpSymbol fnSymbol = (SExpSymbol) function;
        if (fnSymbol.equals(new SExpSymbol("-")) && sExpList.getArgs().size() == 2) {
            // this is a negation
            Symbol1<SInt, SInt> callFn = Symbol1.IntsNegate;
            SMTExpression<?> argument_untyped = sExpList.get(1).accept(this);
            SMTExpression<SInt> argument =
                (SMTExpression<SInt>) argument_untyped;
            Call1<SInt, SInt> result = new Call1<>(callFn, argument);
            return result;
        }
        throw new RuntimeException("not implemented");
    }

    @Override
    public SMTExpression<?> visit(SExpNumeral sExpNumeral) {
        return Ints.constant(sExpNumeral.getBigInteger());
    }

    @Override
    public SMTExpression<?> visit(SExpString sExpString) {
        throw new RuntimeException("not implemented");
    }

    @Override
    public SMTExpression<?> visit(SExpSymbol sExpSymbol) {
        throw new RuntimeException("not implemented");
    }
}
