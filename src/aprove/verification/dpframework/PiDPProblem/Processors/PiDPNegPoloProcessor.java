package aprove.verification.dpframework.PiDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.NegativePolynomials.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.PiDPProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * QDP Polo processor. Tries to orient P and all usable rules of P non-strictly
 * and at least one rule of P strictly, then deletes the strictly oriented
 * rules from P.
 *
 * @author Rene Thiemann
 * @version $Id$
 */
public class PiDPNegPoloProcessor extends PiDPProblemProcessor {

//    private static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPNegPoloProcessor");

    private final int range;
    private final int restriction;
    private final boolean allstrict;

    @ParamsViaArgumentObject
    public PiDPNegPoloProcessor(Arguments arguments) {
        this.range = arguments.range;
        this.restriction = arguments.restriction;
        this.allstrict = arguments.allstrict;
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
        NegPOLOSolver solver = new DynamicNegPOLOSolver(this.range, this.restriction, true, aborter);
        Pair<? extends Order<TRSTerm>, Set<GeneralizedRule>> result = solver.solve(pidp, this.allstrict);

        if (result == null) {
            return ResultFactory.unsuccessful();
        } else {
            Order<TRSTerm> solvingOrder = result.x;
            Set<GeneralizedRule> usableRules = result.y;

            // check which elements of P have been oriented strictly
            Set<GeneralizedRule> newPRules, deletedPRules;
            newPRules = new LinkedHashSet<GeneralizedRule>();
            deletedPRules = new LinkedHashSet<GeneralizedRule>();
            for (GeneralizedRule rule : pidp.getP()) {
                // only add non-strictly oriented rules
                if (! solvingOrder.inRelation(afs.filterTerm(rule.getLeft()), afs.filterTerm(rule.getRight()))) {
                    newPRules.add(rule);
                } else {
                    deletedPRules.add(rule);
                }
            }

            if (Globals.useAssertions) {
                for (GeneralizedRule rule : usableRules) {
                    Constraint<TRSTerm> constraint;
                    constraint = Constraint.create(rule.getLeft(),
                        rule.getRight(), OrderRelation.GE);
                    assert (solvingOrder.solves(afs.filterConstraint(constraint)));
                }
                assert(! deletedPRules.isEmpty());
            }

            // build smaller subproblem and proof (for PiDPProblem there is only one subproblem)
            PiDPProblem newPidp = pidp.getSubProblem(ImmutableCreator.create(newPRules));
            Proof proof = new PiDPOrderProof(deletedPRules, solvingOrder, usableRules);
            return ResultFactory.proved(newPidp, YNMImplication.EQUIVALENT, proof);
        }
    }

    @Override
    public boolean isPiDPApplicable(AbstractPiDPProblem qdp) {
        return qdp instanceof PiDPProblem;
    }


    private static final class PiDPOrderProof extends Proof.DefaultProof {

        private Set<GeneralizedRule> orientedPRules;
        private Set<GeneralizedRule> usableRules;
        private Order<TRSTerm> order;

        private PiDPOrderProof (Set<GeneralizedRule> orientedPRules, Order<TRSTerm> order, Set<GeneralizedRule> usableRules) {
            this.orientedPRules = orientedPRules;
            this.order = order;
            this.usableRules = usableRules;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (true) {
                result.append("We use the reduction pair processor of "+o.cite(Citation.LOPSTR)+". By using an ordering, the following Dependency Pairs of this PiDP problem " +
                                "can be strictly oriented.\n");
                result.append(o.cond_linebreak());
                result.append(o.set(this.orientedPRules, Export_Util.RULES));
                result.append("Used ordering:  ");
                result.append(o.export(this.order));
                result.append(o.cond_linebreak());
                result.append("The following usable rules were oriented:\n");
                result.append(o.set(this.usableRules, Export_Util.RULES));
                result.append(o.cond_linebreak());
            }
            return result.toString();
        }
    }

    public static class Arguments {
        public int range = 1;
        public int restriction = 2;
        public boolean allstrict = false;
    }
}
