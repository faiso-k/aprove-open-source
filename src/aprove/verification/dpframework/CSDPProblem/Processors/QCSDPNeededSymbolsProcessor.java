package aprove.verification.dpframework.CSDPProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
import aprove.verification.dpframework.CSDPProblem.Solvers.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import immutables.*;

public class QCSDPNeededSymbolsProcessor
        extends QCSDPProcessor {

    private final SolverFactory factory;
    private final boolean allstrict;

    @ParamsViaArgumentObject
    public QCSDPNeededSymbolsProcessor(Arguments arguments) {
        this.factory = arguments.order;
        this.allstrict = arguments.allstrict;
    }

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem obl) {
        return true;
    }

    @Override
    protected Result processQCSDP(QCSDPProblem problem, Abortion aborter)
            throws AbortionException {
        // assert that produced order is Ce-compatible. maybe change to
        // conditional inclusion of Ce-rules in checked weakly decreasing set of
        // rules.
        assert (this.factory.solversGenerateCECompatibleOrders());

        ReplacementMap rm = problem.getReplacementMap();
        boolean stronglyConservative = false;

        Set<Rule> neededRules = null;

        // first check if P is strongly conservative
        if (rm.isStronglyConservative(problem.getDp())) {
            neededRules = QCSDPNeededSymbolsProcessor.computeNeededRulesForStronglyConservativeP(problem);

            // if our needed rules are strongly conservative too, they are all
            // we need to consider.
            if (rm.isStronglyConservative(neededRules)) {
                stronglyConservative = true;
            }
        }

        if (stronglyConservative == false) {
            neededRules = QCSDPNeededSymbolsProcessor.computeNeededRules(problem);
        }

        Map<Rule, QActiveCondition> activeR = QUsableRules
                .getRulesAsConditionMap(neededRules);
        QActiveSolver solver = this.factory.getQActiveSolver();

        // ugly.
        if (solver instanceof QCSDPNegCoeffPoloSolver) {
            QCSDPNegCoeffPoloSolver csSolver = (QCSDPNegCoeffPoloSolver) solver;
            csSolver.setMu(problem.getReplacementMap());
        }

        QActiveOrder order = solver.solveQActive(problem.getDp(), activeR, false,
                this.allstrict, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful();
        }

        if (Globals.useAssertions) {
            // check that all pairs are weakly decreasing
            for (Rule rule : problem.getDp()) {
                assert (order.solves(Constraint.fromRule(rule, OrderRelation.GE)));
            }
            // check that all needed rules are weakly decreasing
            for (Rule rule : neededRules) {
                assert (order.solves(Constraint.fromRule(rule, OrderRelation.GE)));
            }

            // check that both Ce rules are weakly decreasing
            // FIXME how to do this _after_ the order is created?
        }

        return this.getResult(problem, neededRules, order, stronglyConservative);
    }

    private Result getResult(QCSDPProblem problem, Set<Rule> neededRules,
            QActiveOrder order, boolean stronglyConservative)
            throws AbortionException {

        Set<Rule> keptPairs = new LinkedHashSet<Rule>();
        Set<Rule> removedPairs = new LinkedHashSet<Rule>();
        for (Rule pair : problem.getDp()) {
            if (order.solves(Constraint.fromRule(pair, OrderRelation.GR))) {
                removedPairs.add(pair);
            } else {
                keptPairs.add(pair);
            }
        }

        if (Globals.useAssertions) {
            assert (!removedPairs.isEmpty());
        }

        QCSDPProblem newp = QCSDPProblem.create(ImmutableCreator
                .create(keptPairs), problem);

        QCSDPReductionPairProof proof = new QCSDPReductionPairProof(
                neededRules, keptPairs, removedPairs, order,
                stronglyConservative);

        return ResultFactory.proved(newp, YNMImplication.EQUIVALENT, proof);
    }

    private class QCSDPReductionPairProof
            extends Proof.DefaultProof {

        private final Set<Rule> neededRules;

        private final Set<Rule> keptPairs;

        private final Set<Rule> removedPairs;

        private final QActiveOrder order;

        private boolean stronglyConservative;

        public QCSDPReductionPairProof(Set<Rule> neededRules,
                Set<Rule> keptPairs, Set<Rule> removedPairs,
                QActiveOrder order, boolean stronglyConservative) {
            this.neededRules = neededRules;
            this.keptPairs = keptPairs;
            this.removedPairs = removedPairs;
            this.order = order;
            this.stronglyConservative = stronglyConservative;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();

            sb.append(o.export("Using the order") + o.newline());
            sb.append(o.export(this.order) + o.newline());
            sb.append(o.export("the following usable rules" + o.newline()));
            sb.append(o.set(this.neededRules, Export_Util.RULES) + o.newline());
            sb.append(o.export("could all be oriented weakly.") + o.newline());

            if (this.stronglyConservative) {
                sb.append(o.export("Since all dependency pairs and these "
                        + "rules are strongly conservative, this is sound.")
                        + o.newline());
            }

            sb.append(o.export("Furthermore, the pairs") + o.newline());
            sb.append(o.set(this.removedPairs, Export_Util.RULES) + o.newline());
            sb.append(o.export("could be oriented strictly and thus removed "
                    + "by the CS-Reduction Pair Processor ")
                    + o.cite(new Citation[] { Citation.LPAR08,
                            Citation.DA_EMMES }) + "." + o.newline());


            return sb.toString();
        }
    }

    private static Set<Rule> computeNeededRulesForStronglyConservativeP(
            QCSDPProblem d) {
        ReplacementMap rm = d.getRm();
        ImmutableSet<Rule> p = d.getDp();

        ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> ruleMap = d
                .getRWithQ().getRuleMap();

        // check this set of rules for all needed rules...
        HashMap<FunctionSymbol, ImmutableSet<Rule>> unneededRuleMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<Rule>>();
        unneededRuleMap.putAll(ruleMap);
        LinkedHashSet<Rule> neededRules = new LinkedHashSet<Rule>();

        for (Rule rule : p) {
            QCSDPNeededSymbolsProcessor.checkRuleForStronglyConservativeP(rm, unneededRuleMap, neededRules,
                    rule);
        }

        return neededRules;

    }

    private static void checkRuleForStronglyConservativeP(ReplacementMap rm,
            HashMap<FunctionSymbol, ImmutableSet<Rule>> unneededRuleMap,
            Set<Rule> neededRules, Rule rule) {
        TRSTerm rhs = rule.getRight();

        // check all replacing positions on the rhs
        for (TRSTerm t : rm.getReplacingSubterms(rhs)) {
            if (!t.isVariable()) {
                TRSFunctionApplication s = (TRSFunctionApplication) t;
                FunctionSymbol f = s.getRootSymbol();
                Set<Rule> addedRules = unneededRuleMap.get(f);
                if (addedRules == null) {
                    continue;
                }
                unneededRuleMap.remove(f);
                neededRules.addAll(addedRules);
                for (Rule nextrule : addedRules) {
                    QCSDPNeededSymbolsProcessor.checkRule(rm, unneededRuleMap, neededRules, nextrule);
                }
            }
        }
    }

    private static Set<Rule> computeNeededRules(QCSDPProblem d) {
        ReplacementMap rm = d.getRm();
        ImmutableSet<Rule> p = d.getDp();
        ImmutableSet<Rule> r = d.getR();

        ImmutableSet<FunctionSymbol> hiddenP = rm.computeHiddenSymbols(p);
        ImmutableSet<FunctionSymbol> hiddenR = rm.computeHiddenSymbols(r);

        ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> ruleMap = d
                .getRWithQ().getRuleMap();

        // add all pairs and all rules from R headed by any hidden symbol
        Set<Rule> seedRules = new LinkedHashSet<Rule>(p);
        Set<FunctionSymbol> syms = new LinkedHashSet<FunctionSymbol>();
        syms.addAll(hiddenP);
        syms.addAll(hiddenR);
        for (FunctionSymbol s : syms) {
            if (ruleMap.containsKey(s)) {
                seedRules.addAll(ruleMap.get(s));
            }
        }

        // check this set of rules for all needed rules...
        HashMap<FunctionSymbol, ImmutableSet<Rule>> unneededRuleMap = new LinkedHashMap<FunctionSymbol, ImmutableSet<Rule>>();
        unneededRuleMap.putAll(ruleMap);
        LinkedHashSet<Rule> neededRules = new LinkedHashSet<Rule>();

        for (Rule rule : seedRules) {
            QCSDPNeededSymbolsProcessor.checkRule(rm, unneededRuleMap, neededRules, rule);
        }

        // add rules rooted by the seed syms
        for (FunctionSymbol s : syms) {
            if (ruleMap.containsKey(s)) {
                neededRules.addAll(ruleMap.get(s));
            }
        }

        return neededRules;
    }

    private static void checkRule(ReplacementMap rm,
            HashMap<FunctionSymbol, ImmutableSet<Rule>> unneededRuleMap,
            Set<Rule> neededRules, Rule rule) {
        TRSTerm lhs = rule.getLeft();
        TRSTerm rhs = rule.getRight();

        // check all non-replacing positions on the lhs
        for (TRSTerm t : rm.getNonReplacingSubterms(lhs)) {
            if (!t.isVariable()) {
                TRSFunctionApplication s = (TRSFunctionApplication) t;
                FunctionSymbol f = s.getRootSymbol();
                Set<Rule> addedRules = unneededRuleMap.get(f);
                if (addedRules == null) {
                    continue;
                }
                unneededRuleMap.remove(f);
                neededRules.addAll(addedRules);
                for (Rule nextrule : addedRules) {
                    QCSDPNeededSymbolsProcessor.checkRule(rm, unneededRuleMap, neededRules, nextrule);
                }
            }
        }

        // check all replacing positions on the rhs
        for (TRSTerm t : rm.getReplacingSubterms(rhs)) {
            if (!t.isVariable()) {
                TRSFunctionApplication s = (TRSFunctionApplication) t;
                FunctionSymbol f = s.getRootSymbol();
                Set<Rule> addedRules = unneededRuleMap.get(f);
                if (addedRules == null) {
                    continue;
                }
                unneededRuleMap.remove(f);
                neededRules.addAll(addedRules);
                for (Rule nextrule : addedRules) {
                    QCSDPNeededSymbolsProcessor.checkRule(rm, unneededRuleMap, neededRules, nextrule);
                }
            }
        }
    }

    public static class Arguments {
        public SolverFactory order;
        public boolean allstrict;
        public boolean mergeMutual; // FIXME do we need merge mutual?
    }
}
