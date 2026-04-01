package aprove.verification.oldframework.SMT.Solver.Z3;

import java.util.*;

import com.microsoft.z3.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.Sort;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;

public class Z3ExpToSMTExpression {

    private List<Symbol0<?>> vars = new LinkedList<>();
    private Model model;
    private SMTExpression<? extends Sort> res;

    public Z3ExpToSMTExpression(Expr e, Model model) throws Z3Exception, SMTFeatureUnavailableException {
        this.model = model;
        this.res = this.transform(e);
        this.vars.sort((x, y) -> x.toString().compareTo(y.toString()));
    }

    public SMTExpression<? extends Sort> getRes() {
        return this.res;
    }

    public List<Symbol0<?>> getVars() {
        return vars;
    }

    private SMTExpression<? extends Sort> transform(Expr e) throws Z3Exception, SMTFeatureUnavailableException {
        if (e.isVar()) {
            return this.caseVar(e);
        }
        if (e.isIntNum()) {
            return this.caseInt(e);
        }
        if (e.isTrue()) {
            return Core.True;
        }
        if (e.isFalse()) {
            return Core.False;
        }
        if (e.isITE()) {
            return this.caseITE(e);
        }
        if (e.isEq()) {
            return this.caseEq(e);
        }
        if (e.isGE()) {
            return this.caseGE(e);
        }
        if (e.isAdd()) {
            return this.caseAdd(e);
        }
        if (e.isSub()) {
            return this.caseSub(e);
        }
        if (e.isMul()) {
            return this.caseMul(e);
        }
        FuncDecl decl = e.getFuncDecl();
        if (decl.getArity() == 0) {
            return this.caseConstant(e);
        } else {
            return this.caseFunApp(e);
        }
    }

    private SMTExpression<? extends Sort> caseFunApp(Expr e) throws Z3Exception, SMTFeatureUnavailableException {
        return this.transform(this.model.getFuncInterp(e.getFuncDecl()).getElse());
    }

    private SMTExpression<? extends Sort> caseConstant(Expr e) throws Z3Exception, SMTFeatureUnavailableException {
        return this.transform(this.model.getConstInterp(e.getFuncDecl()));
    }

    private SMTExpression<? extends Sort> caseMul(Expr e) throws Z3Exception, SMTFeatureUnavailableException {
        return this.caseLeftAssocCall(e, LeftAssocSymbol.IntsTimes);
    }

    private SMTExpression<? extends Sort> caseSub(Expr e) throws Z3Exception, SMTFeatureUnavailableException {
        return this.caseLeftAssocCall(e, LeftAssocSymbol.IntsSubtract);
    }

    private SMTExpression<? extends Sort> caseAdd(Expr e) throws Z3Exception, SMTFeatureUnavailableException {
        return this.caseLeftAssocCall(e, LeftAssocSymbol.IntsAdd);
    }

    private SMTExpression<? extends Sort> caseLeftAssocCall(Expr e, LeftAssocSymbol<SInt, SInt> symbol) throws Z3Exception, SMTFeatureUnavailableException {
        List<SMTExpression<SInt>> args = new LinkedList<>();
        for (final Expr arg : e.getArgs()) {
            args.add((SMTExpression<SInt>) this.transform(arg));
        }
        return new LeftAssocCall<>(symbol, args.get(0), ImmutableCreator.create(args.subList(1, args.size())));
    }

    private SMTExpression<? extends Sort> caseGE(Expr e) throws Z3Exception, SMTFeatureUnavailableException {
        return this.caseBinOp(e, ChainableSymbol.IntsGreaterEqual);
    }

    private SMTExpression<? extends Sort> caseEq(Expr e) throws Z3Exception, SMTFeatureUnavailableException {
        return this.caseBinOp(e, ChainableSymbol.Equivalent);
    }

    private <OperandType extends Sort>
            SMTExpression<? extends Sort>
            caseBinOp(Expr e, ChainableSymbol<OperandType> binFunc) throws Z3Exception, SMTFeatureUnavailableException {
        List<SMTExpression<OperandType>> args = new LinkedList<>();
        for (Expr arg : e.getArgs()) {
            args.add((SMTExpression<OperandType>) this.transform(arg));
        }
        return new ChainableCall<>(binFunc, ImmutableCreator.create(args));
    }

    private SMTExpression<? extends Sort> caseITE(Expr e) throws Z3Exception, SMTFeatureUnavailableException {
        SMTExpression<SBool> cond = (SMTExpression<SBool>) this.transform(e.getArgs()[0]);
        SMTExpression<Sort> thenCase = (SMTExpression<Sort>) this.transform(e.getArgs()[1]);
        SMTExpression<Sort> elseCase = (SMTExpression<Sort>) this.transform(e.getArgs()[2]);
        return new Call3<>(Symbol3.ITE, Sort.representative, cond, thenCase, elseCase);
    }

    private SMTExpression<? extends Sort> caseInt(Expr e) throws Z3Exception {
        return Ints.constant(((IntNum) e).getBigInteger());
    }

    private SMTExpression<? extends Sort> caseVar(Expr e) throws Z3Exception, SMTFeatureUnavailableException {
        Symbol0<?> result;
        if (e.getSort() instanceof IntSort) {
            result = SInt.representative.createVariable(e.toString());
        } else if (e.getSort() instanceof BoolSort) {
            result = SBool.representative.createVariable(e.toString());
        } else {
            throw new SMTFeatureUnavailableException();
        }
        if (!this.vars.contains(result)) {
            this.vars.add(result);
        }
        return result;
    }

}
