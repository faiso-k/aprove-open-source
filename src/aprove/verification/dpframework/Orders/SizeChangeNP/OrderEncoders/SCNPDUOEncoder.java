package aprove.verification.dpframework.Orders.SizeChangeNP.OrderEncoders;

import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class SCNPDUOEncoder implements SCNPOrderEncoder {

    private final SCNPOrderEncoder encoder1;
    private final SCNPOrderEncoder encoder2;
    private final FormulaFactory<None> ff;
    private final Variable<None> flag;
    private final Formula<None> notFlag;

    public SCNPDUOEncoder(FormulaFactory<None> formulaFactory, SolverFactory solver1, SolverFactory solver2) {
        this.ff = formulaFactory;
        this.encoder1 = solver1.getSCNPOrderEncoder(formulaFactory);
        this.encoder2 = solver2.getSCNPOrderEncoder(formulaFactory);
        this.flag = this.ff.buildVariable();
        this.notFlag = this.ff.buildNot(this.flag);
    }

    @Override
    public QActiveOrder decode(int[] satModel, Abortion aborter) throws AbortionException {
        int end = satModel.length;
        int flag = this.flag.getId();
        for (int i = 0; i < end; i++) {
            int value = satModel[i];
            if (value == -flag) {
                return this.encoder1.decode(satModel, aborter);
            } else if (value == flag) {
                return this.encoder2.decode(satModel, aborter);
            }
        }
        assert(false);
        return null;
    }

    @Override
    public Formula<None> encode(Constraint<TRSTerm> c, Abortion aborter) throws AbortionException {
        return this.combine(this.encoder1.encode(c, aborter), this.encoder2.encode(c, aborter));
    }

    @Override
    public Formula<None> encodeQActiveAtom(FunctionSymbol f, int i, Abortion aborter) throws AbortionException {
        return this.combine(this.encoder1.encodeQActiveAtom(f, i, aborter), this.encoder2.encodeQActiveAtom(f, i, aborter));
    }

    @Override
    public FormulaFactory<None> getFormulaFactory() {
        return this.ff;
    }

    @Override
    public Formula<None> post(Abortion aborter) throws AbortionException {
        return this.combine(this.encoder1.post(aborter), this.encoder2.post(aborter));
    }

    @Override
    public Formula<None> pre(Set<FunctionSymbol> sig, Abortion aborter) throws AbortionException {
        return this.combine(this.encoder1.pre(sig, aborter), this.encoder2.pre(sig, aborter));
    }

    @Override
    public Formula<None> toFinalFormula(Formula<None> f, Abortion aborter) throws AbortionException {
        f = this.encoder1.toFinalFormula(f, aborter);
        f = this.encoder2.toFinalFormula(f, aborter);
        return f;
    }

    private Formula<None> combine(Formula<None> f1, Formula<None> f2) {
        f1 = this.ff.buildOr(this.flag, f1);
        f2 = this.ff.buildOr(this.notFlag, f2);
        return this.ff.buildAnd(f1,f2);
    }

}
