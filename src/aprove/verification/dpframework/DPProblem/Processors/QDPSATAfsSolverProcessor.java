package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.dpframework.Orders.SAT.PLEncoders.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

/**
 * @version $Id$
 * @deprecated use ReductionPairProcessor and QDPSATPOSolver instead!
 */
@Deprecated
public class QDPSATAfsSolverProcessor extends QDPProblemProcessor {

    private final static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPSATAfsSolverProcessor");

    private final SolverFactory factory;
    private final boolean active;
    private final boolean unary;

    @ParamsViaArgumentObject
    public QDPSATAfsSolverProcessor(Arguments arguments) {
        this.active = arguments.active;
        this.unary = arguments.unary;
        this.factory = arguments.order;
    }

    public boolean isActive() {
        return this.active;
    }

    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter)
    throws AbortionException {

        // is it allowed to restrict to usable rules?
        final boolean useUsable = qdp.getInnermost() || qdp.getMinimal();
        final boolean useActive = this.active && useUsable;


        long time = System.nanoTime();
        ImmutableSet<Rule> dps = qdp.getP();
        Map<Rule, QActiveCondition> active = null;
        Set<Rule> usableRules = null;
        if (useActive) {
            QUsableRules used = qdp.getQUsableRulesCalculator();
            active = used.getActiveConditions(dps);
        } else {
            usableRules = useUsable ? qdp.getUsableRules() : qdp.getR();
            active = QUsableRules.getRulesAsConditionMap(usableRules);
        }
        time = System.nanoTime()-time;
        long total = time;
        QDPSATAfsSolverProcessor.log.log(Level.FINER, "Computing usable rules: {0} ms\n", time/1000000);

        time = System.nanoTime();
        FormulaFactory<None> formulaFactory = new FullSharingFlatteningFactory<None>();
        SATEncoder encoder = this.factory.getSATEncoder(formulaFactory);
        if (encoder == null) {
            return ResultFactory.notApplicable();
        }
        aborter.checkAbortion();
        POFormula poFormula;
        if (!useActive) {
            poFormula = encoder.encode(dps, usableRules, aborter);
        } else {
            poFormula = encoder.encode(dps, active, true, false, aborter);
        }
        time = System.nanoTime()-time;
        total += time;
        long encodeTime = time;
        QDPSATAfsSolverProcessor.log.log(Level.FINER, "Encoding to partial order constraints: {0} ms\n", time/1000000);

//        System.out.println(poFormula);
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
        QDPSATAfsSolverProcessor.log.log(Level.FINER, "Encoding to propositional logic: {0} ms\n", time/1000000);

        time = System.nanoTime();
        int res[];
        aborter.checkAbortion();
        SATChecker satChecker = this.factory.getSATCheckerFactory().getSATChecker();
        try {
            res = satChecker.solve(formula, aborter);
        } catch (SolverException e) {
            return ResultFactory.unsuccessful();
        }
        time = System.nanoTime()-time;
        total += time;
        QDPSATAfsSolverProcessor.log.log(Level.FINER, "SAT solving: {0} ms\n", time/1000000);
        // TODO make this a regular solver instead of a special processor
        if (res != null) {

            time = System.nanoTime();
            Set<Variable<None>> knownTrue = poFormula.decode(res, formula.getId());
            Afs afs = encoder.getAfs(knownTrue);
            ExportableOrder<TRSTerm> order = encoder.getOrder(knownTrue, afs);
            time = System.nanoTime()-time;
            total += time;
            QDPSATAfsSolverProcessor.log.log(Level.FINER, "Decoding Afs and LPO: {0} ms\n", time/1000000);


            if (useActive) {
                usableRules = qdp.getQUsableRulesCalculator().getUsableRules(dps, afs);
            }

            return QDPReductionPairProcessor.getResult(order, usableRules, qdp,
                    null);
        }
        QDPSATAfsSolverProcessor.log.log(Level.FINE, "Total time: {0} ms\n", total/1000000);
        //qdp.dumpCodish(encodeTime, solveTime, decodeTime, 1, 0, "failed", null, null);
        return ResultFactory.unsuccessful();
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return true;
    }

    public static class Arguments {
        public boolean active = true;
        public boolean unary = false;
        public SolverFactory order;
    }

}
