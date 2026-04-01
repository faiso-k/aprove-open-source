package aprove.verification.dpframework.IDPProblem.Processors.nonInf;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.orders.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.IConstraintGenerator.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

public class IDPNonInfProcessor extends IDPProcessor {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.IDPProblem.Processors.nonInf.IDPNonInfProcessor");

    protected final IdpIUsableSolver solver;

    @ParamsViaArgumentObject
    public IDPNonInfProcessor(final Arguments arguments) {
        this.solver = arguments.solver;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        if (false && this.solver instanceof IDPGPoloSolver) {
            // DEACTIVATED QUICKFIX FOR NAT INCORRECTNESS
            final IDPGPoloSolver s = (IDPGPoloSolver) this.solver;
            if (s.getIsNat()) {
                IDPNonInfProcessor.log.warning("IDPNonInf with parameter \"Nat = True\" has been deactivated for maintenance purposes!");
                return false;
            }
        }
        final HashSet<Domain> allowedDomains = new LinkedHashSet<Domain>();

        allowedDomains.add(DomainFactory.INTEGERS);
        allowedDomains.add(DomainFactory.BOOLEAN);

        return idp.getRuleAnalysis().isNfQSubsetEqNfR() && (allowedDomains.containsAll(idp.getRuleAnalysis().getDomains()));
    }

    @Override
    protected Result processIDPProblem(final IDPProblem origIdp, final Abortion aborter) throws AbortionException {
        try {
            // is it allowed to restrict to usable rules?

            IdpQUsableRules usableRules;
            usableRules = origIdp.getRuleAnalysis().getUseableRules(null);

            aborter.checkAbortion();
            final INonInfOrder solvingOrder = (INonInfOrder) this.solver.solve(origIdp, usableRules, aborter);
            if (solvingOrder != null) {
                return this.getResult(solvingOrder, usableRules, origIdp);
            }
            return ResultFactory.unsuccessful();
        }
        catch (final UnsupportedOperationException e) {
            // this try-catch-code probably should not stay here forever
            if (aprove.Globals.aproveVersion == aprove.Globals.AproveVersion.DEVELOPER_VERSION) {
                System.err.println("UnsupportedOperationException occurred in idp noninf!");
                System.err.println(e);
                System.err.println("Input: ");
                System.err.println(origIdp);
                System.err.println("Config: ");
                System.err.println(this.solver);
                e.printStackTrace();
            }
            throw e;
        }
    }

//  public Pair<? extends ExportableOrder<Term>, Set<GeneralizedRule>> solve(QDPProblem transQDP, Abortion aborter) throws AbortionException;

    /**
     * Standard method to compute the result of a reduction pair processor.
     * @param order
     * @param protoUsableRules
     * @param origIDP
     * @param atransformer null, if no a-transformation, mapping from P to A(P) and U(P,R) to A(U(P,R))
     * @return
     */
    public Result getResult(
            final INonInfOrder order,
            final IdpQUsableRules usableRules,
            final IDPProblem origIdp) throws AbortionException {

        Set<GeneralizedRule> deletedBoundRules, deletedPRules;
        deletedPRules = new LinkedHashSet<GeneralizedRule>();
        deletedBoundRules = new LinkedHashSet<GeneralizedRule>();
        for (final Node node : origIdp.getIdpGraph().getNodes()) {
            if (order.orientsStrictly(node.rule)) {
                deletedPRules.add(node.rule);
            }
        }
        for (final Node node : origIdp.getIdpGraph().getNodes()) {
            if (order.nonInf_lhsGEConst(node.rule)) {
                deletedBoundRules.add(node.rule);
            }
        }

        if (deletedPRules.isEmpty() || deletedBoundRules.isEmpty()) {
            return ResultFactory.unsuccessful();
        }
        /*
        Set<GeneralizedRule> deletedIntersection = new LinkedHashSet<GeneralizedRule>(deletedPRules);
        deletedIntersection.retainAll(deletedBoundRules);
        if (!deletedIntersection.isEmpty()) {
            deletedPRules = deletedBoundRules = deletedIntersection;
        }*/

        // in case P_> and P_bound are in some kind of subset relation
        // between one another, it suffices to return a single IDP problem

        // check which elements of P have been oriented strictly
        Set<GeneralizedRule> newPRules;
        final Set<Node> newPNodes = new LinkedHashSet<Node>();
        newPRules = new LinkedHashSet<GeneralizedRule>();
        for (final Node node : origIdp.getIdpGraph().getNodes()) {
            // only add non-strictly oriented rules
            if (!deletedPRules.contains(node.rule)) {
                newPRules.add(node.rule);
                newPNodes.add(node);
            }
        }

        // check which lhs of elements of P are greater than constant c
        Set<GeneralizedRule> newBoundRules;
        final Set<Node> newBoundNodes = new LinkedHashSet<Node>();
        newBoundRules = new LinkedHashSet<GeneralizedRule>();
        for (final Node node : origIdp.getIdpGraph().getNodes()) {
            // only add non-strictly oriented rules
            if (!deletedBoundRules.contains(node.rule)) {
                newBoundRules.add(node.rule);
                newBoundNodes.add(node);
            }
        }

        final Map<GeneralizedRule, Map<RelDependency, IDirection>> usableMap = order.getOrientedUsables();

        // build smaller subproblem and proof
        final Set<IDPProblem> newProblems = new LinkedHashSet<IDPProblem>();
        if (deletedBoundRules.containsAll(deletedPRules)) {
            // P_> \subseteq P_bound => we only need (P \ P_>, R)
            final IDPProblem newIdpP = origIdp.change(origIdp.getIdpGraph().restrictToNodes(newPNodes, YNM.MAYBE, this), null, null, null, this);
            newProblems.add(newIdpP);
        }
        else if (deletedPRules.containsAll(deletedBoundRules)) {
            // P_bound \subset(eq) P_> => we only need (P \ P_bound, R)
            final IDPProblem newIdpBound = origIdp.change(origIdp.getIdpGraph().restrictToNodes(newBoundNodes, YNM.MAYBE, this), null, null, null, this);
            newProblems.add(newIdpBound);
        }
        else { // we need both IDP problems
            final IDPProblem newIdpP = origIdp.change(origIdp.getIdpGraph().restrictToNodes(newPNodes, YNM.MAYBE, this), null, null, null, this);
            newProblems.add(newIdpP);
            final IDPProblem newIdpBound = origIdp.change(origIdp.getIdpGraph().restrictToNodes(newBoundNodes, YNM.MAYBE, this), null, null, null, this);
            newProblems.add(newIdpBound);
        }
        final Proof proof = new IDPNonInfProof(origIdp, deletedPRules, deletedBoundRules, newPRules, order, usableMap, order.getConstraintsProof(), this.solver);
        return ResultFactory.provedAnd(newProblems, YNMImplication.SOUND, proof);
    }

    static final class IDPNonInfProof extends Proof.DefaultProof {

        private final Set<GeneralizedRule> orientedPRules;
        private final Set<GeneralizedRule> orientedPBoundRules;
        private final Set<GeneralizedRule> keptPRules;
        private final Map<GeneralizedRule, Map<RelDependency, IDirection>> usableRules;
        private final ExportableOrder<TRSTerm> order;
        private final IDPProblem origIDP;
        private final IConstraintGeneratorProof constraintsProof;
        private final IdpIUsableSolver solver;

        IDPNonInfProof (
                final IDPProblem origIDP,
                final Set<GeneralizedRule> orientedPRules,
                final Set<GeneralizedRule> orientedPBoundRules,
               final Set<GeneralizedRule> keptPRules,
                final ExportableOrder<TRSTerm> order,
                final Map<GeneralizedRule, Map<RelDependency, IDirection>> usableMap,
                final IConstraintGeneratorProof constraintsProof,
                final IdpIUsableSolver solv) {
            this.orientedPRules = orientedPRules;
            this.orientedPBoundRules = orientedPBoundRules;
            this.order = order;
            this.keptPRules = keptPRules;
            this.usableRules = usableMap;
            this.origIDP = origIDP;
            this.constraintsProof = constraintsProof;
            this.solver = solv;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (true) {
                result.append("Used the following options for this NonInfProof:");
                result.append(o.newline());
                result.append(this.solver);
                result.append(o.newline());
                result.append(o.newline());

                result.append("The constraints were generated the following way:");
                result.append(o.newline());
                result.append(this.constraintsProof.export(o));
                result.append(o.newline());


                result.append("Using the following integer polynomial ordering the "
                        + " resulting constraints can be solved ");
                result.append(o.newline());
                result.append(this.order.export(o));
                result.append(o.newline());

                result.append("The following pairs are in P" + o.sub(o.gtSign()) + ":");
                result.append(o.newline());
                result.append(o.set(this.orientedPRules, Export_Util.RULES));
                result.append(o.newline());
                result.append("The following pairs are in P" + o.sub("bound") + ":");
                result.append(o.newline());
                result.append(o.set(this.orientedPBoundRules, Export_Util.RULES));
                result.append(o.newline());
                result.append("The following pairs are in P" + o.sub(o.geSign()) + ":");
                result.append(o.newline());
                result.append(o.set(this.keptPRules, Export_Util.RULES));
                result.append(o.newline());
                if (this.usableRules.isEmpty()) {
                    result.append("There are no usable rules.");
                } else {
                    result.append("At least the following rules have been oriented under context sensitive arithmetic replacement:");
                    result.append(o.cond_linebreak());
                    final List<String> usables = new ArrayList<String>(this.usableRules.size());
                    final IDPPredefinedMap predefinedMap = this.origIDP.getRuleAnalysis().getPreDefinedMap();
                    for (final Map.Entry<GeneralizedRule, Map<RelDependency, IDirection>> usable
                            : this.usableRules.entrySet()) {
                        final GeneralizedRule rule = usable.getKey();
                        for (final Map.Entry<RelDependency, IDirection> ruleOrient : usable.getValue().entrySet()) {
                            final IDirection dir = ruleOrient.getValue();
                            final RelDependency dependency = ruleOrient.getKey();
                            final PredefinedFunction func = predefinedMap.getPredefinedFunction(rule.getLeft().getRootSymbol());
                            if (func != null && !func.hasFiniteRuleSet()) {
                                final StringBuilder sb = new StringBuilder();
                                sb.append(rule.getLeft().getRootSymbol().export(o));
                                sb.append(o.sup(dependency.getK().toString()));
                                sb.append(" ");
                                if (dir == IDirection.Both) {
                                    sb.append(o.leftrightarrow());
                                } else if (dir == IDirection.Reversed) {
                                    sb.append(o.leftarrow());
                                } else if (dir == IDirection.Normal) {
                                    sb.append(o.rightarrow());
                                } else if (dir == IDirection.None) {
                                    sb.append("filtered");
                                }
                                usables.add(sb.toString());
                            } else if (dir != IDirection.None) {
                                TRSTerm left, right;
                                if (dir == IDirection.Reversed) {
                                    left = rule.getRight();
                                    right = rule.getLeft();
                                } else {
                                    left = rule.getLeft();
                                    right = rule.getRight();
                                }
                                final StringBuilder sb = new StringBuilder();
                                sb.append(left.export(o));
                                sb.append(o.sup(dependency.getK().toString()));
                                sb.append(" ");
                                sb.append((dir == IDirection.Both ? o.leftrightarrow() : o.rightarrow()));
                                sb.append(" ");
                                sb.append(right.export(o));
                                sb.append(o.sup(dependency.getK().toString()));
                                usables.add(sb.toString());
                            }
                        }
                    }
                    result.append(o.set(usables, Export_Util.RULES));
                }
            }
            return result.toString();
        }

    }

    public static class Arguments {
        public IdpIUsableSolver solver = null;
    }

}
