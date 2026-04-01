package aprove.verification.dpframework.Orders.SizeChangeNP.OrderEncoders;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Encode the constraints for the embedding order.
 * No search involved => very small formulae (0 or 1)!
 *
 * @author Carsten Fuhs
 */
public class SCNPEmbEncoder implements SCNPOrderEncoder {

    private FormulaFactory<None> ffactory;
    private Formula<None> ZERO;
    private Formula<None> ONE;

    public SCNPEmbEncoder(FormulaFactory<None> ffactory) {
        this.ffactory = ffactory;
        this.ZERO = this.ffactory.buildConstant(false);
        this.ONE = this.ffactory.buildConstant(true);
    }

    @Override
    public QActiveOrder decode(int[] satModel, Abortion aborter)
            throws AbortionException {
        Afs noAfs = new Afs();
        AfsOrder result = new AfsOrder(noAfs, EMB.theEMB);
        return result;
    }

    @Override
    public Formula<None> encode(Constraint<TRSTerm> c, Abortion aborter)
            throws AbortionException {
        boolean solved = EMB.theEMB.solves(c);
        return solved ? this.ONE : this.ZERO;
    }

    @Override
    public Formula<None> encodeQActiveAtom(FunctionSymbol f, int i, Abortion aborter) throws AbortionException {
        // no filtering in plain old EMB
        return this.ONE;
    }

    @Override
    public FormulaFactory<None> getFormulaFactory() {
        return this.ffactory;
    }

    @Override
    public Formula<None> post(Abortion aborter) throws AbortionException {
        return this.ONE; // yay!
    }

    @Override
    public Formula<None> pre(Set<FunctionSymbol> sig,
            Abortion aborter) throws AbortionException {
        return this.ONE; // yay!
    }

    @Override
    public Formula<None> toFinalFormula(Formula<None> f, Abortion aborter)
            throws AbortionException {
        return f;
    }
}
