package aprove.verification.diophantine;

import java.io.*;
import java.math.*;
import java.util.*;

import aprove.*;
import aprove.cli.Generic.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author kabasci
 * @version $Id$
 */
public class DioconstraintExecutor extends ProblemExecutor {

    private final DioOptions opts;

    private final Reader problemReader;
    private Map<String, BigInteger> res = null;

    public DioconstraintExecutor(final Reader problemReader, final DioOptions opts) {
        super(opts);
        this.problemReader = problemReader;
        this.opts = opts;
    }

    @Override
    public synchronized void printResult(final PrintWriter out) {
        if (!this.done) {
            // Must have gotten here through abort()
            if (Globals.useAssertions) {
                assert (this.abort.isAborted()) : "printResult() called before DiophantineExecutor finished";
            }
            out.println("TIMEOUT\n");
        } else {
            if (this.res == null) {
                out.println("+NO solution.");
            } else {
                out.println("+SOLUTION:");
                for (final Map.Entry<String, BigInteger> entry : this.res.entrySet()) {
                    out.println("+ " + entry.getKey() + " = " + entry.getValue());
                }
                out.println("-");
            }
            if (this.trackTime) {
                out.println("TIME: " + (this.millisAtFinish - this.millisAtStart) + " ms.");
            }
        }
    }

    @Override
    public void solve() throws AbortionException {
        final DefaultValueMap<String, BigInteger> allRanges =
            new DefaultValueMap<String, BigInteger>(this.opts.getRange());
        final SearchAlgorithm searchAlg = EngineHack.getSearchAlg(this.opts.getStrategyString(), allRanges);
        this.res = SimpleDiophantineSolver.solve(this.problemReader, searchAlg, this.verbose, this.abort);
    }
}
