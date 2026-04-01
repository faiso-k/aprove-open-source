package aprove.verification.dpframework.CSDPProblem.Processors;

import static aprove.verification.dpframework.BasicStructures.Utility.PoloStrictMode.*;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolyConstraintSimplifier.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Context-sensitive Rule Removal processor.
 * Using a mu-monotonic POLO, tries to orient all rules of P
 * and R non-strictly and at least one rule of P or R strictly, then
 * deletes the strictly oriented rules. (See Theorem 30 of LPAR04
 * for the corresponding non-context-sensitive case.)
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class QCSDPPoloRuleRemovalProcessor extends QCSDPProcessor {

    private final static Logger log = Logger.getLogger("aprove.verification.dpframework.CSDPProblem.Processors.QCSDPPoloRuleRemovalProcessor");

    private final PoloStrictMode mode; // searchstrict, autostrict, allstrict

    private final POLOFactory factory;

    @ParamsViaArgumentObject
    public QCSDPPoloRuleRemovalProcessor(Arguments arguments) {
        this.mode = arguments.mode;

        POLOFactory.Arguments facArgs = new POLOFactory.Arguments();
        facArgs.degree = arguments.degree;
        facArgs.engine = arguments.engine;
        facArgs.maxSimpleDegree = arguments.maxSimpleDegree;
        facArgs.range = arguments.range;
        facArgs.satConverter = arguments.satConverter;
        facArgs.simplification = arguments.simplification;
        facArgs.simplifyAll = arguments.simplifyAll;
        facArgs.stripExponents = arguments.stripExponents;
        this.factory = new POLOFactory(facArgs);

    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.CSDPProblem.Processors.QCSDPProcessor#processQCSDP(aprove.verification.dpframework.CSDPProblem.QCSDPProblem, aprove.strategies.Abortions.Abortion)
     */
    @Override
    protected Result processQCSDP(QCSDPProblem qcsdp, Abortion aborter)
            throws AbortionException {

        ImmutableSet<Rule> r = qcsdp.getR();
        ImmutableSet<Rule> p = qcsdp.getDp();
        ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> mu = qcsdp.getReplacementMap().getMap();
        Order<TRSTerm> solvingOrder;
        Set<Constraint<TRSTerm>> constraints;
        POLOSolver solver;
        QCSDPPoloRuleRemovalProcessor.log.log(Level.FINE, "Using mode: {0}\n", this.mode);
        switch (this.mode) {
        case AUTOSTRICT :
            constraints = Constraint.fromRules(r, OrderRelation.GE);
            constraints.addAll(Constraint.fromRules(p, OrderRelation.GE));
            solver = this.factory.getSolver(constraints);
            solver.setAllowWeakMonotonicity(false);
            solver.setMu(mu);
            Set<VarPolyConstraint> poloConstraints;
            poloConstraints = solver.createPoloConstraints(aborter, constraints);
            solver.addASC(poloConstraints);
            solvingOrder = solver.solve(aborter, poloConstraints);
            break;
        case ALLSTRICT :
            constraints = Constraint.fromRules(r, OrderRelation.GR);
            constraints.addAll(Constraint.fromRules(p, OrderRelation.GR));
            solver = this.factory.getSolver(constraints);
            solver.setAllowWeakMonotonicity(false);
            solver.setMu(mu);
            solvingOrder = solver.solve(constraints, aborter);
            break;
        case SEARCHSTRICT :
            constraints = Constraint.fromRules(r, OrderRelation.GE);
            constraints.addAll(Constraint.fromRules(p, OrderRelation.GE));
            solver = this.factory.getSolver(constraints);
            solver.setAllowWeakMonotonicity(false);
            solver.setMu(mu);
            solvingOrder = solver.solve(new HashSet<Constraint<TRSTerm>>(0),
                    constraints, aborter);
            break;
        default:
            throw new RuntimeException("Unhandled strictness mode " + this.mode);
        }

        return this.processQCSDP(solvingOrder, qcsdp, aborter);
    }

    /**
     * Checks whether some rules in R or P of qdp are oriented strictly
     * by solvingOrder, removes them and generates an according proof.
     *
     * Requires that solvingOrder orients all rules of P and R in qdp at least
     * non-strictly.
     *
     * @param solvingOrder the order which is supposed to orient all rules in
     *  P united with R non-strictly
     * @param qcsdp the QCSDPProblem to simplify
     * @param aborter
     * @return the corresponding result
     */
    protected Result processQCSDP(Order<TRSTerm> solvingOrder, QCSDPProblem qcsdp,
                Abortion aborter) throws AbortionException {
        if (solvingOrder == null) {
            return ResultFactory.unsuccessful();
        }

        ImmutableSet<Rule> p, r;
        p = qcsdp.getDp();
        r = qcsdp.getR();

        // check which elements of P or R have been oriented strictly
        Set<Rule> newPRules, deletedPRules, newRRules, deletedRRules;
        newPRules = new LinkedHashSet<Rule>();
        deletedPRules = new LinkedHashSet<Rule>();
        newRRules = new LinkedHashSet<Rule>();
        deletedRRules = new LinkedHashSet<Rule>();
        for (Rule rule : p) {
            // only add non-strictly oriented rules
            if (! solvingOrder.inRelation(rule.getLeft(), rule.getRight())) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> constraint;
                    constraint = Constraint.create(rule.getLeft(),
                            rule.getRight(), OrderRelation.GE);
                    assert (solvingOrder.solves(constraint));
                }
                newPRules.add(rule);
            }
            else {
                deletedPRules.add(rule);
            }

        }
        for (Rule rule : r) {
            // only add non-strictly oriented rules
            if (! solvingOrder.inRelation(rule.getLeft(), rule.getRight())) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> constraint;
                    constraint = Constraint.create(rule.getLeft(),
                            rule.getRight(), OrderRelation.GE);
                    assert (solvingOrder.solves(constraint));
                }
                newRRules.add(rule);
            }
            else {
                deletedRRules.add(rule);
            }

        }

        if (Globals.useAssertions) {
            assert (! (deletedPRules.isEmpty()
                    && deletedRRules.isEmpty()));
        }

        // build smaller subproblem and the proof
        // different cases to be able to reuse some computed results of the current qdp problem
        QCSDPProblem newQdp;
        if (deletedRRules.isEmpty()) {
            newQdp = QCSDPProblem.create(ImmutableCreator.create(newPRules), qcsdp);
        } else if (deletedPRules.isEmpty()) {
            newQdp = QCSDPProblem.create(qcsdp, ImmutableCreator.create(newRRules));
        } else {
            newQdp = QCSDPProblem.create(ImmutableCreator.create(newPRules),
                    ImmutableCreator.create(newRRules), qcsdp);
        }
        POLO polo = (POLO) solvingOrder;
        Proof proof = new QCSDPMuMonotonicPoloProof(deletedRRules, deletedPRules, polo);
        Result result = ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);
        return result;
    }

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem qdp) {
        return true;
    }

    private static final class QCSDPMuMonotonicPoloProof extends Proof.DefaultProof {

        private Set<Rule> orientedRRules;
        private Set<Rule> orientedPRules;
        private POLO polo;

        private QCSDPMuMonotonicPoloProof (Set<Rule> orientedRRules, Set<Rule> orientedPRules,
                POLO polo) {
            if (Globals.useAssertions) {
                assert(! (orientedPRules.isEmpty()
                        && orientedRRules.isEmpty()));
            }
            this.orientedRRules = orientedRRules;
            this.orientedPRules = orientedPRules;
            this.polo = polo;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (true) { // TODO deal with level
                result.append("By using the following " +
                        o.mu() + "-monotonic polynomial ordering " +
                        o.cite(Citation.POLO) +
                        ", at least one Dependency Pair or term rewrite system rule of this Q-CSDP problem can be strictly oriented and thus deleted.\n");
                result.append(o.cond_linebreak());
                if (! this.orientedPRules.isEmpty()) {
                    result.append("Strictly oriented dependency pairs:\n");
                    result.append(o.set(this.orientedPRules, Export_Util.RULES));
                }
                result.append(o.cond_linebreak());
                if (! this.orientedRRules.isEmpty()) {
                    result.append("Strictly oriented rules of the TRS R:\n");
                    result.append(o.set(this.orientedRRules, Export_Util.RULES));
                }
                result.append(o.cond_linebreak());
                result.append("Used ordering: POLO with ");
                result.append(this.polo.export(o));
                result.append(o.cond_linebreak());
            }
            return result.toString();
        }
    }

    public static class Arguments {
        public PoloStrictMode mode = AUTOSTRICT;
        public int degree;
        public Engine engine;
        public int maxSimpleDegree;
        public int range;
        public DiophantineSATConverter satConverter;
        public SimplificationMode simplification;
        public boolean simplifyAll;
        public boolean stripExponents;
    }

}
