package aprove.verification.dpframework.DPProblem.Processors;

import static aprove.verification.dpframework.BasicStructures.Utility.PoloStrictMode.*;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * QDP Polo processor. Tries to orient P and all usable rules of P non-strictly
 * and at least one rule of P strictly, then deletes the strictly oriented
 * rules from P.
 *
 * @author Carsten Fuhs
 * @version $Id$
 *
 * @deprecated use QDPReductionPairProcessor and QDPPoloSolver instead
 */
@Deprecated
public class QDPPoloProcessor extends AbstractStrictPoloQDPProblemProcessor {

    private static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPPoloProcessor");

    private final boolean active;      // should we use active if applicable?
    private final boolean mergeMutual; // should we use merge mutual heuristic when using
                                       // active? (smaller active conditions, but less power)

    @ParamsViaArgumentObject
    public QDPPoloProcessor(Arguments arguments) {
        super(arguments);
        this.active = arguments.active;
        this.mergeMutual = arguments.mergeMutual;
    }

    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter)
            throws AbortionException {

        // is it allowed to restrict to usable rules?
        final boolean useUsable = qdp.getInnermost() || qdp.getMinimal();



        ImmutableSet<Rule> p = qdp.getP();

        // should we use active?
        boolean useActive = this.active && useUsable;
        Map<Rule,QActiveCondition> usableRules;
        if (useActive) {
            usableRules = qdp.getQUsableRulesCalculator().getActiveConditions(p, this.mergeMutual);
        } else {
            Set<Rule> uR = useUsable ? qdp.getUsableRules() : qdp.getR();
            usableRules = QUsableRules.getRulesAsConditionMap(uR);
        }
        POLO solvingOrder;
        POLOSolver solver;
        PoloStrictMode mode = (p.size() == 1) ? ALLSTRICT : this.mode;
        QDPPoloProcessor.log.log(Level.FINE, "Using mode: {0}\n", mode);

        Set<Constraint<TRSTerm>> pConstraints = Constraint.fromRules(p, mode == ALLSTRICT ? OrderRelation.GR : OrderRelation.GE);
        Triple<POLOSolver, Set<SimplePolyConstraint>, Set<VarPolyConstraint>> solverTriple =
            this.factory.getSolver(pConstraints, usableRules, null, null, aborter);

        solver = solverTriple.x;
        solver.setAllowWeakMonotonicity(true);
        Set<SimplePolyConstraint> noSearchConstraints1 = solverTriple.y;
        Set<VarPolyConstraint> noSearchConstraints2 = solverTriple.z;
        Set<VarPolyConstraint> PConstraints = solver.createPoloConstraints(aborter, pConstraints);
        Set<VarPolyConstraint> searchConstraints;
        switch (mode) {
        case AUTOSTRICT :
            solver.addASC(PConstraints);
            noSearchConstraints2.addAll(PConstraints);
            searchConstraints = null;
            break;
        case ALLSTRICT :
            noSearchConstraints2.addAll(PConstraints);
            searchConstraints = null;
            break;
        case SEARCHSTRICT :
            searchConstraints = PConstraints;
            break;
        default:
            return ResultFactory.notApplicable();
        }
        try {
            solvingOrder = solver.solve(noSearchConstraints1, noSearchConstraints2, searchConstraints, aborter);
        } catch (BuiltTooManyException e) {
            return ResultFactory.unsuccessful();
        }

        if (solvingOrder == null) {
//            qdp.dumpCodish(SatSearch.encodeTime, SatSearch.solveTime, SatSearch.decodeTime, 1, 0, "failed", null, null);
            return ResultFactory.unsuccessful();
        }


        Set<Rule> UsableRules = new LinkedHashSet<Rule>(usableRules.size());
        Interpretation inter = solvingOrder.getInterpretation();
        for (Map.Entry<Rule, QActiveCondition> usableRule : usableRules.entrySet()) {
            SimplePolynomial condition = inter.getActiveConstraint(usableRule.getValue());
            if (condition.equals(SimplePolynomial.ONE)) {
                UsableRules.add(usableRule.getKey());
            } else if (!condition.equals(SimplePolynomial.ZERO)) {
                if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                    String message = "Internal error: having active condition not being 0 or 1 after the polo solution: "+condition;
                    System.err.println(message);
                    System.err.println(qdp.toString());
                    System.err.println(inter);
                    QDPPoloProcessor.log.log(Level.SEVERE, message);
                }

                UsableRules.add(usableRule.getKey());
            }
        }

        return QDPReductionPairProcessor.getResult(solvingOrder, UsableRules,
                qdp, null);
    }


    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return true;
    }

    public static class Arguments extends AbstractStrictPoloQDPProblemProcessor.Arguments {
        public boolean active = true;
        public boolean mergeMutual = true;
    }
}
