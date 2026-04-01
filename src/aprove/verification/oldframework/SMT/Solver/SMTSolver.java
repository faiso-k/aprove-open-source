package aprove.verification.oldframework.SMT.Solver;

import java.io.*;
import java.math.*;
import java.util.*;

import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public interface SMTSolver {

    public void addAssertion(SMTExpression<SBool> formula);

    public YNM checkSAT();

    void declare(Symbol<?> sym);

    Boolean getValue(SBool sort, SMTExpression<SBool> exp);

    BigInteger getValue(SInt sort, SMTExpression<SInt> exp);

    ArrayList<Boolean> getValues(SBool sort, Iterable<SMTExpression<SBool>> exps);

    ArrayList<BigInteger> getValues(SInt sort, Iterable<SMTExpression<SInt>> exps);

    public void pop();

    public void push();

    /**
     * Using this solver after calling this method leads to undefined results.
     * Used to free resources, before they are claimed by the GC.
     * @throws IOException
     */
    public void dispose() throws IOException;

    /**
     * Returns a list of currently asserted expressions that are Unsat. This
     * list is not necessarily minimal, but it should be better than returning
     * all assertions.
     * <p>This must only be called directly after {@link #checkSAT()} returned
     * {@code No}.
     * @return
     */
    ArrayList<SMTExpression<SBool>> getUnsatCore();
}
