package aprove.verification.dpframework.TRSProblem.Solvers;

import java.util.*;
import java.util.logging.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.dpframework.Orders.SAT.PLEncoders.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 * SAT encoder and solver for RRR termination problems with path orders.
 * Tries to find an ordering that satisfies l >= r for all rules and l > r for at least one rule.
 *
 * Assumes that the concrete solver used is always applicable.
 * Change isApplicable() if necessary.
 *
 * @author Andreas Kelle-Emden
 * @version $Id$
 */
public class SATRRRSolver implements RRRSolver {

    private static Logger log = Logger.getLogger("aprove.verification.dpframework.TRSPRoblem.Solvers.SATRRRSolver");

    private SolverFactory factory;
    private boolean unary = false;

    public SATRRRSolver(SolverFactory factory) {
        this.factory = factory;
    }

    @Override
    public boolean isRRRApplicable(Set<Rule> R) {
        return true;
    }

    @Override
    public ExportableOrder<TRSTerm> solveRRR(Set<Rule> R, Abortion aborter) throws AbortionException {
        long time = System.nanoTime();
        FormulaFactory<None> formulaFactory = new FullSharingFlatteningFactory<None>();
        SATEncoder encoder = this.factory.getSATEncoder(formulaFactory);
        if (encoder == null || !(encoder instanceof AbstractPOEncoder)) {
            return null;
        }
        aborter.checkAbortion();

        SATChecker satChecker = this.factory.getSATCheckerFactory().getSATChecker();
        POFormula poFormula = null;
        List<Formula<None>> maxSatList = null;
        if (satChecker instanceof MaxSATChecker) {
            Pair<POFormula, List<Formula<None>>> pair = ((AbstractPOEncoder)encoder).encodeMaxSATRRR(R, aborter);
            poFormula = pair.x;
            maxSatList = pair.y;
        } else {
            poFormula = ((AbstractPOEncoder)encoder).encodeRRR(R, aborter);
        }

        time = System.nanoTime()-time;
        long total = time;
        SATRRRSolver.log.log(Level.FINER, "Encoding to partial order constraints: {0} ms\n", time/1000000);

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
        SATRRRSolver.log.log(Level.FINER, "Encoding to propositional logic: {0} ms\n", time/1000000);

        time = System.nanoTime();
        int res[] = null;
        aborter.checkAbortion();
        if (satChecker instanceof MaxSATChecker) {
            res = ((MaxSATChecker)satChecker).solve(formula, maxSatList, aborter);
        } else {
            try {
                res = satChecker.solve(formula, aborter);
            } catch (SolverException e) {
                return null;
            }
        }
        time = System.nanoTime()-time;
        total += time;
        SATRRRSolver.log.log(Level.FINER, "SAT solving: {0} ms\n", time/1000000);
        if (res != null) {

            time = System.nanoTime();
            Set<Variable<None>> knownTrue = poFormula.decode(res, formula.getId());
            Afs afs = encoder.getAfs(knownTrue);
            ExportableOrder<TRSTerm> order = encoder.getOrder(knownTrue, afs);
            time = System.nanoTime()-time;
            total += time;
            SATRRRSolver.log.log(Level.FINER, "Decoding Afs and PO: {0} ms\n", time/1000000);

            return order;
        }
        SATRRRSolver.log.log(Level.FINE, "Total time: {0} ms\n", total/1000000);
        return null;
    }

}
