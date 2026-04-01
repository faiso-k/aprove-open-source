package aprove.verification.idpframework.Processors.NonInf.Solving;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import immutables.*;

/**
 *
 * @author MP
 */
public interface ItpfPolyConstraintsSolver {

    public static enum SolverType {
        SAT_SOLVER {
            @Override
            public ItpfPolyConstraintsSolver getSolver() {
                return new ItpfPolyDiophantineSatSolver();
            }
        },

        SMT_SOLVER {
            @Override
            public ItpfPolyConstraintsSolver getSolver() {
                return new ItpfPolyDiophantineSmtSolver();
            }
        },

        SAT_SMT_SOLVER {
            @Override
            public ItpfPolyConstraintsSolver getSolver() {
                final ArrayList<ItpfPolyConstraintsSolver> solverList = new ArrayList<ItpfPolyConstraintsSolver>();
                solverList.add(SAT_SOLVER.getSolver());
                solverList.add(SMT_SOLVER.getSolver());
                return new ItpfPolyConstraintSolverAny(ImmutableCreator.create(solverList));
            }
        };

        public abstract ItpfPolyConstraintsSolver getSolver();
    }


    /**
     * @param implications conjunction of implications
     * @param aborter TODO
     * @return
     */
    PolyInterpretation<BigInt> solve(IDPPredefinedMap predefinedMap, PolyInterpretation<BigInt> abstractInterpretation,
        Conjunction<Itpf> constraints, Abortion aborter) throws AbortionException;

}
