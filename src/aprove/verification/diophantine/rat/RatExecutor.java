package aprove.verification.diophantine.rat;

import java.io.*;
import java.util.*;

import aprove.*;
import aprove.cli.Generic.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 *
 * @author bearperson
 * @version $Id$
 */
public class RatExecutor<C extends GPolyCoeff> extends ProblemExecutor {

    private final GPolyCoeffFactory<C> creator;

    private final Reader problemReader;
    private final OPCRange<C> range;
    private Map<String, String> res = null;
    private final OPCSolver<C> solver;

    public RatExecutor(
        final Reader problemReader,
        final OPCSolver<C> solver,
        final OPCRange<C> range,
        final GPolyCoeffFactory<C> creator,
        final RatOptions opts)
    {
        super(opts);
        this.problemReader = problemReader;
        this.solver = solver;
        this.range = range;
        this.creator = creator;
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
                for (final Map.Entry<String, String> entry : this.res.entrySet()) {
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
            SimpleRatSolver.solve(this.problemReader, this.solver, this.range, this.creator, this.verbose, this.abort);
    }
}
