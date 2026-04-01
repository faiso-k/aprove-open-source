package aprove.verification.dpframework.DPProblem.Solvers;

import java.util.*;
import java.util.logging.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.dpframework.Orders.SAT.PLEncoders.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

public class QDPSATPOSolver implements QActiveSolver {

    public static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPSATAfsSolverProcessor");

    private SolverFactory factory;
    private boolean unary = false;

    public QDPSATPOSolver(SolverFactory factory) {
        this.factory = factory;
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R, boolean active, boolean allstrict, Abortion aborter) throws AbortionException {
        long time = System.nanoTime();
        FormulaFactory<None> formulaFactory = new FullSharingFlatteningFactory<None>();
        SATEncoder encoder = this.factory.getSATEncoder(formulaFactory);
        if (encoder == null) {
            return null;
        }
        aborter.checkAbortion();
        POFormula poFormula = encoder.encode(P, R, active, allstrict, aborter);
        time = System.nanoTime()-time;
        long total = time;
        long encodeTime = time;
        QDPSATPOSolver.log.log(Level.FINER, "Encoding to partial order constraints: {0} ms\n", time/1000000);

        time = System.nanoTime();
        aborter.checkAbortion();
        PLEncoder plEncoder;
        if (!this.unary) {
            plEncoder = new SimpleBinaryPLEncoder(formulaFactory, encoder.isAllowQuasi());
        } else {
            plEncoder = new SimpleUnaryPLEncoder(formulaFactory, encoder.isAllowQuasi());
        }
        Formula<None> formula = plEncoder.toPropositionalFormula(poFormula, aborter);
        time = System.nanoTime()-time;
        total += time;
        encodeTime += time;
        QDPSATPOSolver.log.log(Level.FINER, "Encoding to propositional logic: {0} ms\n", time/1000000);

        time = System.nanoTime();
        int res[];
        aborter.checkAbortion();
        SATChecker satChecker = this.factory.getSATCheckerFactory().getSATChecker();
        try {
            res = satChecker.solve(formula, aborter);
        } catch (SolverException e) {
            return null;
        }
        time = System.nanoTime()-time;
        total += time;
        QDPSATPOSolver.log.log(Level.FINER, "SAT solving: {0} ms\n", time/1000000);
        if (res != null) {

            time = System.nanoTime();
            Set<Variable<None>> knownTrue = poFormula.decode(res, formula.getId());
            Afs afs = encoder.getAfs(knownTrue);
            QActiveOrder order = encoder.getOrder(knownTrue, afs);
            time = System.nanoTime()-time;
            total += time;
            QDPSATPOSolver.log.log(Level.FINER, "Decoding Afs and LPO: {0} ms\n", time/1000000);

            return order;
        }
        QDPSATPOSolver.log.log(Level.FINE, "Total time: {0} ms\n", total/1000000);
        return null;
    }

}
