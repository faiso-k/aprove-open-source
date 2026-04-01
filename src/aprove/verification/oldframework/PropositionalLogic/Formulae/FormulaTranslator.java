package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.io.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.PropositionalLogic.Translation.*;

public class FormulaTranslator extends MemorizingDepthFirstFormulaVisitor<None> {


    Tseitinizer out;

    // The next ID to label a node with.
    // 1 is reserved for true, 2 for false.
    int nextId = 3;
    public static final int TRUE_ID = 1;
    public static final int FALSE_ID = 2;



    // Have there been any errors on the way?
    IOException ex = null;

    // Helper array to save space; we grow it like an arrayList.
    private int[] clause = new int[4];


    public FormulaTranslator(Tseitinizer out) throws IOException {
        out.pushFalse(FormulaTranslator.FALSE_ID);
        out.pushTrue(FormulaTranslator.TRUE_ID);
        this.out = out;
    }

    public void finish(Formula<None> masterFormula) throws IOException {
        if (this.ex != null) {
            throw this.ex;
        }
        this.out.pushTrue(masterFormula.getId());
    }

    /**
     * Resize the array as needed; at least double its size each time to avoid doing this too often.
     * @param newSize The new required size.
     */
    private void redimArray(final int newSize) {
        if (this.clause.length < newSize) {
            this.clause = new int[newSize > this.clause.length * 2 ? newSize : this.clause.length * 2];
        }
    }


    // override those methods which we need to act in, which are only the out methods for action.
    // Note that this class is not guaranteed to work if a non-DAG is provided!


    @Override
    protected void outAnd(AndFormula<None> f) {

        f.labelThisWith(this.nextId);
        this.nextId++;
        this.redimArray(f.args.size());
        int i=0;
        for (Formula<None> ff: f.args ) {
            this.clause[i] = ff.getId();
            i++;
        }
        try {
            this.out.pushAnd(f.getId(), this.clause, i);
        } catch (IOException ex) {
            this.ex = ex;
        }

    }

    @Override
    protected void outOr(OrFormula<None> f) {

        f.labelThisWith(this.nextId);
        this.nextId++;
        this.redimArray(f.args.size());
        int i=0;
        for (Formula<None> ff: f.args ) {
            this.clause[i] = ff.getId();
            i++;
        }
        try {
            this.out.pushOr(f.getId(), this.clause, i);
        } catch (IOException ex) {
            this.ex = ex;
        }

    }

    @Override
    protected void outXor(XorFormula<None> f) {

        f.labelThisWith(this.nextId);
        this.nextId++;
        this.redimArray(f.args.size());
        int i=0;
        for (Formula<None> ff: f.args ) {
            this.clause[i] = ff.getId();
            i++;
        }
        try {
            this.out.pushXOr(f.getId(), this.clause, i);
        } catch (IOException ex) {
            this.ex = ex;
        }

    }

    @Override
    protected void outIff(IffFormula<None> f) {

        f.labelThisWith(this.nextId);
        this.nextId++;
        try {
            this.out.pushIff(f.getId(), f.left.getId(), f.right.getId());
        } catch (IOException ex) {
            this.ex = ex;
        }

    }

    @Override
    protected void outIte(IteFormula<None> f) {

        f.labelThisWith(this.nextId);
        this.nextId++;
        try {
            this.out.pushITE(f.getId(), f.condition.getId(), f.thenFormula.getId(), f.elseFormula.getId());
        } catch (IOException ex) {
            this.ex = ex;
        }

    }

    @Override
    protected void outNot(NotFormula<None> f) {

        f.labelThisWith(-f.arg.getId());

    }

    @Override
    protected void outConstant(Constant<None> f) {

        if (f.getValue()) {
            f.labelThisWith(FormulaTranslator.TRUE_ID);
        } else {
            f.labelThisWith(FormulaTranslator.FALSE_ID);
        }

    }

    @Override
    protected void outVariable(Variable<None> f) {
        f.labelThisWith(this.nextId);
        this.nextId++;
    }

    @Override
    protected void outAtLeast(AtLeastFormula<None> f) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }

    @Override
    protected void outAtMost(AtMostFormula<None> f) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }

    @Override
    protected void outCount(CountFormula<None> f) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }

}
