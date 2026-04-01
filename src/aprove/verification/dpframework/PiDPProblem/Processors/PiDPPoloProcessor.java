package aprove.verification.dpframework.PiDPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.PiDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * PiDP Polo processor. Tries to orient P and all usable rules of P
 * non-strictly and at least one rule of P strictly, then deletes the strictly
 * oriented rules from P; all this after the application of the afs Pi.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class PiDPPoloProcessor extends AbstractStrictPoloPiDPProblemProcessor {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.PiDPPoloProcessor");

    @ParamsViaArgumentObject
    public PiDPPoloProcessor(Arguments arguments) {
        super(arguments);
    }

    @Override
    protected Result processPiDPProblem(AbstractPiDPProblem apidp,
        Abortion aborter)
            throws AbortionException {
        if (Globals.useAssertions) {
            assert (this.isApplicable(apidp));
        }
        PiDPProblem pidp = (PiDPProblem) apidp;
        Afs afs = pidp.getPi();
        POLOSolver solver;
        ImmutableSet<GeneralizedRule> usableRules = pidp.getUsableRules();
        ImmutableSet<GeneralizedRule> p = pidp.getP();
        Order<TRSTerm> solvingOrder;
        Set<Constraint<TRSTerm>> constraints;
        constraints = Constraint.fromRules(usableRules, OrderRelation.GE);
        constraints = afs.filterConstraints(constraints);
        PoloStrictMode mode;
        mode = (p.size() == 1) ? PoloStrictMode.ALLSTRICT : this.mode;
        PiDPPoloProcessor.log.log(Level.FINE, "Using mode: {0}\n", mode);
        switch (this.mode) {
        case AUTOSTRICT :
            Set<Constraint<TRSTerm>> pConstraints, allConstraints;
            pConstraints = Constraint.fromRules(p, OrderRelation.GE);
            pConstraints = afs.filterConstraints(pConstraints);
            allConstraints = new LinkedHashSet<Constraint<TRSTerm>>(constraints);
            allConstraints.addAll(pConstraints);
            solver = this.factory.getSolver(allConstraints);
            Set<VarPolyConstraint> poloCs, pPoloCs;
            pPoloCs = solver.createPoloConstraints(aborter, pConstraints);
            solver.addASC(pPoloCs);
            poloCs = solver.createPoloConstraints(aborter, constraints);
            poloCs.addAll(pPoloCs);
            solver.setAllowWeakMonotonicity(true);
            solvingOrder = solver.solve(aborter, poloCs);
            break;
        case ALLSTRICT :
            pConstraints = afs.filterConstraints(Constraint.fromRules(p, OrderRelation.GR));
            constraints.addAll(pConstraints);
            solver = this.factory.getSolver(constraints);
            solver.setAllowWeakMonotonicity(true);
            solvingOrder = solver.solve(constraints, aborter);
            break;
        case SEARCHSTRICT :
            Set<Constraint<TRSTerm>> searchStrictConstraints;
            searchStrictConstraints = afs.filterConstraints(Constraint.fromRules(p, OrderRelation.GE));
            allConstraints = new LinkedHashSet<Constraint<TRSTerm>>(constraints);
            allConstraints.addAll(searchStrictConstraints);
            solver = this.factory.getSolver(allConstraints);
            solver.setAllowWeakMonotonicity(true);
            solvingOrder = solver.solve(constraints,
                    searchStrictConstraints, aborter);
            break;
        default:
            return ResultFactory.notApplicable();
        }
        if (solvingOrder == null) {
            return ResultFactory.unsuccessful();
        }

        // check which elements of P have been oriented strictly
        Set<GeneralizedRule> newPRules, deletedPRules;
        newPRules = new LinkedHashSet<GeneralizedRule>();
        deletedPRules = new LinkedHashSet<GeneralizedRule>();
        for (GeneralizedRule rule : p) {
            // only add non-strictly oriented rules
            if (! solvingOrder.inRelation(afs.filterTerm(rule.getLeft()), afs.filterTerm(rule.getRight()))) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> constraint;
                    constraint = Constraint.create(afs.filterTerm(rule.getLeft()),
                            afs.filterTerm(rule.getRight()), OrderRelation.GE);
                    assert (solvingOrder.solves(constraint));
                }
                newPRules.add(rule);
            }
            else {
                deletedPRules.add(rule);
            }

        }
        if (Globals.useAssertions) {
            for (GeneralizedRule rule : usableRules) {
                Constraint<TRSTerm> constraint;
                constraint = Constraint.create(afs.filterTerm(rule.getLeft()),
                        afs.filterTerm(rule.getRight()), OrderRelation.GE);
                assert (solvingOrder.solves(constraint));
            }
            assert(! deletedPRules.isEmpty());
        }

        // build smaller subproblem and proof
        PiDPProblem newPidp =
            pidp.getSubProblem(ImmutableCreator.create(newPRules));
        POLO polo = (POLO) solvingOrder;
        Proof proof = new PiDPPoloProof(deletedPRules, polo, newPidp);
        Result result = ResultFactory.proved(newPidp, YNMImplication.EQUIVALENT, proof);

        return result;
    }


    @Override
    public boolean isPiDPApplicable(AbstractPiDPProblem apidp) {
        return apidp instanceof PiDPProblem;
    }


    private static final class PiDPPoloProof extends Proof.DefaultProof {

        private PiDPProblem pidp;
        private Set<GeneralizedRule> orientedPRules;
        private POLO polo;

        private PiDPPoloProof(Set<GeneralizedRule> orientedPRules, POLO polo,
                PiDPProblem resultingPidp) {
            this.orientedPRules = orientedPRules;
            this.polo = polo;
            this.pidp = resultingPidp;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (true) { // TODO level wants some attn
                result.append("By using the reduction pair processor "+o.cite(Citation.LOPSTR)+", at least one Dependency Pair of this Pi-DP problem can be strictly oriented.\n");
                result.append(o.cond_linebreak());
                result.append(o.set(this.orientedPRules, Export_Util.RULES));
                result.append("Used ordering: ");
                result.append(this.polo.export(o));
                /*
                int numberOfSccs = qdp.getDependencyGraph().getSubSCCs().size();
                result.append(" resulting in "+ProofUtility.number(numberOfSccs));
                result.append(" subcycle"+ProofUtility.ending(numberOfSccs)+".\n");
                */
                result.append(o.cond_linebreak());
            }
            return result.toString();
        }
    }
}
