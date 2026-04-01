package aprove.verification.idpframework.Processors.NonInf.Solving;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.oldframework.Utility.Multithread.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class ItpfPolyConstraintSolverAny implements ItpfPolyConstraintsSolver {

    private final ImmutableCollection<ItpfPolyConstraintsSolver> solvers;

    public ItpfPolyConstraintSolverAny(final ImmutableCollection<ItpfPolyConstraintsSolver> solvers) {
        this.solvers = solvers;

    }

    @Override
    public PolyInterpretation<BigInt> solve(final IDPPredefinedMap predefinedMap,
        final PolyInterpretation<BigInt> abstractInterpretation,
        final Conjunction<Itpf> constraints,
        final Abortion aborter) throws AbortionException {

        final List<SolverWorker> workers =
                new ArrayList<SolverWorker>();

        for (final ItpfPolyConstraintsSolver solver : this.solvers) {
            workers.add(new SolverWorker(solver, predefinedMap, abstractInterpretation, constraints));
        }

        final SolverWorker succesfulSolver = MultithreadedExecutor.executeUntilError(workers, aborter);

        if (succesfulSolver != null) {
            return succesfulSolver.getResult();
        } else {
            return null;
        }
    }


    private static class SolverWorker implements AbortableRunnable {

        private PolyInterpretation<BigInt> result;

        private final ItpfPolyConstraintsSolver solver;
        private final IDPPredefinedMap predefinedMap;
        private final PolyInterpretation<BigInt> abstractInterpretation;
        private final Conjunction<Itpf> constraints;

        public SolverWorker(final ItpfPolyConstraintsSolver solver,
                final IDPPredefinedMap predefinedMap,
                final PolyInterpretation<BigInt> abstractInterpretation,
                final Conjunction<Itpf> constraints) {
                    this.solver = solver;
                    this.predefinedMap = predefinedMap;
                    this.abstractInterpretation = abstractInterpretation;
                    this.constraints = constraints;
        }

        public PolyInterpretation<BigInt> getResult() {
            return this.result;
        }

        @Override
        public WorkStatus execute(final Abortion aborter) throws AbortionException {
            this.result = this.solver.solve(this.predefinedMap, this.abstractInterpretation, this.constraints, aborter);
            if (this.result != null) {
                return WorkStatus.FINISH;
            } else {
                return WorkStatus.CONTINUE;
            }
        }

    }
}
