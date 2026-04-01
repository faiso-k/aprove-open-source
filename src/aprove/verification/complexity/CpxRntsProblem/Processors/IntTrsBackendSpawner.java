package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Helper function to run all ITS backends and choose the backend with the best
 * (polynomial) result.
 *
 * @note currently, all backends are run sequentially, which should probably
 * change in the future.
 *
 * @note PUBS is currently not enabled, as the tool is not publicly available.
 * The timeout value for PUBS is thus simply ignored. To enable PUBS, add
 * it to the backends list in `runAll` and adapt `anyBackendInstalled`.
 *
 * @author mnaaf
 *
 */
public abstract class IntTrsBackendSpawner {

    //timeout settings in milliseconds
    public static class Timeouts {
        int pubs = 0;
        int koat = 0;
        int cofloco = 0;
    }

    public static boolean anyBackendInstalled() {
        return CoFloCoBackend.isInstalled || KoATBackend.isInstalled;
    }

    //runs all backends, returns the one with the best bound
    //(where polynomial bounds are only heuristically compared)
    public static IntTrsBackend runAll(CpxRntsProblem its, Abortion a, Timeouts timeouts) {
        //list of backends. Order is important, first ones are preferred
        List<IntTrsBackend> backends = new ArrayList<>();
        if (CoFloCoBackend.isInstalled) {
            backends.add(new CoFloCoBackend(its,a,timeouts.cofloco));
        }
        if (KoATBackend.isInstalled) {
            backends.add(new KoATBackend(its,a,timeouts.koat));
        }

        assert !backends.isEmpty();

        int bestIdx = 0;
        ComplexityValue bestCpx = ComplexityValue.infinite();
        Optional<SimplePolynomial> bestPoly = Optional.empty();
        for (int i=0; i < backends.size(); ++i) {
            a.checkAbortion();
            if (!backends.get(i).run()) {
                continue;
            }
            ComplexityValue cpx = backends.get(i).getComplexity();
            Optional<SimplePolynomial> poly = backends.get(i).getPolynomialBound();

            if (TermHelper.isFirstCpxBetter(cpx,poly, bestCpx,bestPoly)) {
                bestCpx = cpx;
                bestPoly = poly;
                bestIdx = i;
            }
        }

        return backends.get(bestIdx); //choose first prover if all fail
    }

}
