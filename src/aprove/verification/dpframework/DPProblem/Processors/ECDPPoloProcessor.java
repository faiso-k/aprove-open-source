package aprove.verification.dpframework.DPProblem.Processors;

import static aprove.verification.dpframework.BasicStructures.Utility.PoloStrictMode.*;

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
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * EDP Polo processor (Th.4.11 and 4.28 in EDP Framework) in case that E only consists of C Equations
 * and so the improved usavble rules and equations are applicable. Tries to orient P and all improved usable rules
 * of P non-strictly and all improved usable equations and esharp equations equivalently and at least one rule of P strictly,
 * then deletes the strictly oriented rules from P. Improved usable rules / equations can only be
 * used if the order is Ce-kompatible and f=m, otherwise all rules of R / E must be oriented.
 *
 * @author stein
 * @version $Id$
 */
public class ECDPPoloProcessor extends EAbstractStrictPoloEDPProblemProcessor {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.ECDPPoloProcessor");

    @ParamsViaArgumentObject
    public ECDPPoloProcessor(Arguments arguments) {
        super(arguments);
    }

    @Override
    protected Result processEDPProblem(EDPProblem edp, Abortion aborter)
            throws AbortionException {

        if(edp.getRwithE().checkC()) {

            // is it allowed to restrict to usable rules?
            final boolean useUsable =  edp.getMinimal();

            ImmutableSet<Rule> p = edp.getP();
            ImmutableSet<Equation> esharp = edp.getESharp();

            Map<Rule,QActiveCondition> usableRules;
            Map<Equation,QActiveCondition> usableEquations;

            ECUsableRules usableRulesCalc = new ECUsableRules(edp.getRwithE());
            Set<Rule> uR = useUsable ? usableRulesCalc.getUsableRules(edp.getP(), edp.getESharp()) : edp.getR();
            usableRules = EUsableRules.getRulesAsConditionMap(uR);
            Set<Equation> uE = useUsable ? usableRulesCalc.getUsableEquations(edp.getP(), edp.getESharp()) : edp.getE();
            usableEquations = EUsableRules.getEquationsAsConditionMap(uE);

            POLO solvingOrder;
            POLOSolver solver;
            PoloStrictMode mode = (p.size() == 1) ? ALLSTRICT : this.mode;
            ECDPPoloProcessor.log.log(Level.FINE, "Using mode: {0}\n", mode);

            Set<Constraint<TRSTerm>> pConstraints = Constraint.fromRules(p, mode == ALLSTRICT ? OrderRelation.GR : OrderRelation.GE);
            Set<Constraint<TRSTerm>> eSharpConstraints = Constraint.fromEquations(esharp);
            Triple<POLOSolver, Set<SimplePolyConstraint>, Set<VarPolyConstraint>> solverTriple =
                this.factory.getSolver(pConstraints, usableRules,
                        eSharpConstraints, usableEquations, aborter);

            solver = solverTriple.x;
            solver.setAllowWeakMonotonicity(true);
            Set<SimplePolyConstraint> noSearchConstraints1 = solverTriple.y;
            Set<VarPolyConstraint> noSearchConstraints2 = solverTriple.z;
            Set<VarPolyConstraint> PConstraints = solver.createPoloConstraints(aborter, pConstraints);
            Set<VarPolyConstraint> searchConstraints;
            //Add Conditions for esharp equations
            // -> process the equations conventionally since they
            //    have sharped roots
            noSearchConstraints2.addAll(solver.createPoloConstraints(aborter, eSharpConstraints));

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
                        System.err.println(edp.toString());
                        System.err.println(inter);
                        ECDPPoloProcessor.log.log(Level.SEVERE, message);
                    }

                    UsableRules.add(usableRule.getKey());
                }
            }
            Set<Equation> UsableEquations = new LinkedHashSet<Equation>(usableEquations.size());
            for (Map.Entry<Equation, QActiveCondition> usableEqn : usableEquations.entrySet()) {
                SimplePolynomial condition = inter.getActiveConstraint(usableEqn.getValue());
                if (condition.equals(SimplePolynomial.ONE)) {
                    UsableEquations.add(usableEqn.getKey());
                } else if (!condition.equals(SimplePolynomial.ZERO)) {
                    if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                        String message = "Internal error: having active condition not being 0 or 1 after the polo solution: "+condition;
                        System.err.println(message);
                        System.err.println(edp.toString());
                        System.err.println(inter);
                        ECDPPoloProcessor.log.log(Level.SEVERE, message);
                    }

                    UsableEquations.add(usableEqn.getKey());
                }
            }

            return ECDPPoloProcessor.getResult(solvingOrder, UsableRules, UsableEquations, edp);
        }
        else{
            return ResultFactory.notApplicable();
        }
    }

    /**
     * Method to compute the result of a reduction pair processor.
     */
    public static Result getResult(POLO order, Set<Rule> usableRules, Set<Equation> usableEquations, EDPProblem origedp) {

        // check which elements of P have been oriented strictly
        Set<Rule> newPRules, deletedPRules;
        newPRules = new LinkedHashSet<Rule>();
        deletedPRules = new LinkedHashSet<Rule>();

        for (Rule rule : origedp.getP()) {
            // only add non-strictly oriented rules
            if (!order.inRelation(rule.getLeft(), rule.getRight())) {
                newPRules.add(rule);
            } else {
                deletedPRules.add(rule);
            }
        }


        if (Globals.useAssertions) {
            OrderRelation relation = OrderRelation.GE;
            for (Rule rule : usableRules) {
                TRSTerm left = rule.getLeft();
                TRSTerm right = rule.getRight();
                assert (order.solves(Constraint.create(left, right, relation)));
            }
            for (Rule rule : origedp.getP()) {
                TRSTerm left = rule.getLeft();
                TRSTerm right = rule.getRight();
                assert (order.solves(Constraint.create(left, right, relation)));
            }
            relation = OrderRelation.EQ;
            for (Equation eq : usableEquations) {
                TRSTerm left = eq.getLeft();
                TRSTerm right = eq.getRight();
                assert (order.solves(Constraint.create(left, right, relation)));
            }
            for (Equation eq : origedp.getESharp()) {
                TRSTerm left = eq.getLeft();
                TRSTerm right = eq.getRight();
                assert (order.solves(Constraint.create(left, right, relation)));
            }
            assert(! deletedPRules.isEmpty());
        }

        // build smaller subproblem and proof
        EDPProblem newEdp = origedp.getSubProblemWithSmallerP(ImmutableCreator.create(newPRules));
        Proof proof = new ECDPPoloProof(deletedPRules, newPRules, usableRules, origedp.getESharp(), usableEquations, order, newEdp);
        return ResultFactory.proved(newEdp, YNMImplication.EQUIVALENT, proof);
    }


    @Override
    public boolean isEDPApplicable(EDPProblem edp) {
        return edp.getRwithE().checkC();
    }

    private static final class ECDPPoloProof extends Proof.DefaultProof {

        private EDPProblem edp;
        private Set<Rule> strictPRules;
        private Set<Rule> nonStrictPRules;
        private Set<Rule> usableRules;
        private Set<Equation> eSharp;
        private Set<Equation> usableEquations;
        private POLO polo;

        private ECDPPoloProof (Set<Rule> strictPRules, Set<Rule> nonStrictPRules, Set<Rule> usableRules, Set<Equation> eSharp,
                Set<Equation> usableEquations, POLO polo, EDPProblem resultingEdp) {
            this.strictPRules = strictPRules;
            this.nonStrictPRules = nonStrictPRules;
            this.usableRules = usableRules;
            this.eSharp = eSharp;
            this.usableEquations = usableEquations;
            this.polo = polo;
            this.edp = resultingEdp;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuffer result;
            result = new StringBuffer();
            if (true) { // TODO level wants some attn
                boolean didAll = this.nonStrictPRules.isEmpty();
                result.append("We use the reduction pair processor "+o.cite(Citation.DA_STEIN)+
                        " with a polynomial ordering "+o.cite(Citation.POLO)+". " +
                        (didAll ? "All" : "The following set of") +
                        " Dependency Pairs of this DP problem can be strictly oriented.\n");
                result.append(o.cond_linebreak());
                result.append(o.set(this.strictPRules, Export_Util.RULES));
                if (!didAll) {
                    result.append("The remaining Dependency Pairs were at least non-strictly oriented.\n");
                    result.append(o.cond_linebreak());
                    result.append(o.set(this.nonStrictPRules, Export_Util.RULES));
                }

                if (this.usableRules.isEmpty()) {
                    result.append("There is no improved usable rule of R.\n");
                    result.append(o.paragraph());
                } else {
                    result.append("Wwe had to orient the following set of improved usable rules of R non-strictly.\n");
                    result.append(o.cond_linebreak());
                    result.append(o.set(this.usableRules, Export_Util.RULES));
                }

                if (this.eSharp.isEmpty()) {
                    result.append("There is no equation of E#.\n");
                    result.append(o.paragraph());
                } else {
                    result.append("We had to orient the following equations of E# equivalently.\n");
                    result.append(o.cond_linebreak());
                    result.append(o.set(this.eSharp, Export_Util.RULES));
                }

                if (this.usableEquations.isEmpty()) {
                    result.append("There is no usable equation of E.\n");
                    result.append(o.paragraph());
                } else {
                    result.append("We had to orient the following usable equations of E equivalently.\n");
                    result.append(o.cond_linebreak());
                    result.append(o.set(this.usableEquations, Export_Util.RULES));
                }

                result.append("Used ordering: POLO with ");
                result.append(this.polo.export(o));
                /*
                int numberOfSccs = edp.getDependencyGraph().getSubSCCs().size();
                result.append(" resulting in "+ProofUtility.number(numberOfSccs));
                result.append(" subcycle"+ProofUtility.ending(numberOfSccs)+".\n");
                */
                result.append(o.cond_linebreak());
            }
            return result.toString();
        }
    }
}
