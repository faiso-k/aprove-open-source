package aprove.verification.oldframework.IntegerReasoning.smt;

import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;

/**
 * The available SMT solvers used in the frontends.
 * @author cryingshadow
 * @version $Id$
 */
public enum FrontendSMT {

    /**
     * Our own incomplete heuristics.
     */
    HEURISTICS(null, null, LLVMHeuristicStateFactory.LLVM_HEURISTIC_STATE_FACTORY),

    /**
     * SMTInterpol.
     */
    SMTINTERPOLINT(
        new SMTInterpolIntSolverFactory(),
        SMTLIBLogic.QF_LIA,
        LLVMAbstractStateFactory.LLVM_DEFAULT_STATE_FACTORY
    ),

    /**
     * Z3 as external process.
     */
    Z3EXT(new Z3ExtSolverFactory(), SMTLIBLogic.QF_NIA, LLVMAbstractStateFactory.LLVM_DEFAULT_STATE_FACTORY),

    /**
     * Z3 with Java bindings.
     */
    Z3INT(new Z3IntSolverFactory(), SMTLIBLogic.QF_NIA, LLVMAbstractStateFactory.LLVM_DEFAULT_STATE_FACTORY);

    /**
     * The supported logic for the corresponding SMT solver.
     */
    public final SMTLIBLogic smtLogic;

    /**
     * The solver factory.
     */
    public final SMTSolverFactory smtSolverFactory;

    /**
     * The factory to build abstract LLVM states.
     */
    public final LLVMAbstractStateFactory stateFactory;

    /**
     * @param smtFact The solver factory.
     * @param logic The supported logic for the corresponding SMT solver.
     * @param stateFact The factory to build abstract LLVM states.
     */
    private FrontendSMT(SMTSolverFactory smtFact, SMTLIBLogic logic, LLVMAbstractStateFactory stateFact) {
        this.smtSolverFactory = smtFact;
        this.smtLogic = logic;
        this.stateFactory = stateFact;
    }

}
