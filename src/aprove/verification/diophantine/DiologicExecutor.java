package aprove.verification.diophantine;

import java.io.*;
import java.math.*;
import java.util.*;

import aprove.*;
import aprove.cli.Generic.*;
import aprove.strategies.Abortions.*;

public class DiologicExecutor extends ProblemExecutor {
    private final DioOptions opts;

    private final Reader problemReader;
    private Map<String, BigInteger> res = null;

    public DiologicExecutor(final Reader problemReader, final DioOptions opts) {
        super(opts);
        this.opts = opts;
        this.problemReader = problemReader;
    }

    @Override
    public synchronized void printResult(final PrintWriter out) {
        final DioOptions.DioOutputMode outputMode = this.opts.getOutputMode();
        if (!this.done) {
            // Must have gotten here through abort()
            if (Globals.useAssertions) {
                assert (this.abort.isAborted()) : "printResult() called before DiophantineExecutor finished";
            }
            out.println(outputMode.TIMEOUT);
        } else {
            if (this.res == null) {
                out.println(outputMode.MAYBE); //no solution found
                out.println("+NO solution");

            } else {
                out.println(outputMode.YES);

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
        this.res =
            FormulaDiophantineSolver.solve(
                this.problemReader,
                this.opts.getStrategyString(),
                this.opts.getRange(),
                this.verbose,
                this.abort);
    }
}
