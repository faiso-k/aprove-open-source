package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Rule inlining processor for RNTSs
 *
 * Inlines terminating function symbols (no function calls on any rhs), e.g.
 *   p(x) -> x+1 [ x > 0 ])
 * whenever on some rhs, e.g.
 *   f(x) -> f(p(x+1)) is inlined to f(x) -> f(x) -> f((x+1)+1) [(x+1) > 0]
 *
 * A function symbol is terminating iff all outgoing transitions are
 * terminating. Note that in case of multiple outgoing transition, inlining
 * creates multiple rules (for f in the example).
 *
 * Note that this process might be repeated. Consider for example
 * p(x) -> x+1 and g(x) -> p(2*x). After inlining, we have g(x) -> (2*x)+1
 * which can now also be inlined.
 *
 * As inlining often creates unsatisfiable guards, a quick SMT-query is
 * done whenever inlining is performed, and unsatisfiable rules are discarded.
 *
 * @note returns unsuccessful if no inlining step could be performed.
 *
 * @author mnaaf
 *
 */
public class CpxRntsInliningProcessor extends ProcessorSkeleton {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof CpxRntsProblem;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        CpxRntsInliningWorker worker = new CpxRntsInliningWorker();
        Result res = worker.process(obl, oblNode, aborter, rti);
        return res;
    }

    /**
     * Helper class to encapsulate the instance-dependent state of the
     * computation by the processor.
     */
    private static class CpxRntsInliningWorker {

        //heuristic: inlining a terminating function with n rules in k places
        //of a single rule will create n*k new rules, which we bound by this value
        //NOTE: many of the newly created rules are probably unsatisfiable
        private static final int MAX_RULE_BLOWUP = 10;

        //many inlined rules have an unsatisfiable guard, which is detected using
        //SMT queries which should be fast (timeout is in milliseconds)
        private static final int SMT_TIMEOUT = 100;

        private CpxRntsProblem rnts = null;
        private Abortion aborter = null;


        private Optional<Position> findInnermostInlinableFun(FunctionSymbol fun, TRSTerm TRSTerm) {
            if (TRSTerm.isVariable()) return Optional.empty();
            TRSFunctionApplication funapp = (TRSFunctionApplication)TRSTerm;
            for (int i=0; i < funapp.getRootSymbol().getArity(); ++i) {
                Optional<Position> res = findInnermostInlinableFun(fun, funapp.getArgument(i));
                if (res.isPresent()) {
                    Position p = res.get().prepend(i);
                    return Optional.of(p);
                }
            }
            if (funapp.getRootSymbol().equals(fun)) {
                for (TRSTerm arg : funapp.getArguments()) {
                    if (this.rnts.hasDefinedSymbols(arg)) {
                        return Optional.empty();
                    }
                }
                return Optional.of(Position.EPSILON);
            }
            return Optional.empty();
        }

        private Set<RntsRule> inlineAtPos(FunctionSymbol fun, Position pos, RntsRule rule) {

            assert !rule.getRight().getSubterm(pos).isVariable();
            TRSFunctionApplication funapp = (TRSFunctionApplication)rule.getRight().getSubterm(pos);
            assert funapp.getRootSymbol().equals(fun);

            Map<TRSVariable,TRSTerm> submap = new LinkedHashMap<>();
            for (int i=0; i < funapp.getRootSymbol().getArity(); ++i) {
                TRSTerm arg = funapp.getArgument(i);
                assert CpxIntTermHelper.isIntegerTerm(arg) : "Argument is not only arithmetic: " + arg;
                submap.put(TRSTerm.createVariable(this.rnts.getArgumentName(i)), funapp.getArgument(i));
            }
            Substitution subs = TRSSubstitution.create(ImmutableCreator.create(submap));

            Set<RntsRule> res = new LinkedHashSet<>();
            for (RntsRule inlineRuleOrig : this.rnts.getRulesFrom(fun)) {
                RntsRule inlineRule = inlineRuleOrig.renameFreeVariables(rule.getVariables());
                TRSTerm inlineRhs = inlineRule.getRight().applySubstitution(subs);
                TRSTerm rhs = rule.getRight().replaceAt(pos,  inlineRhs);

                Set<Constraint> guard = new LinkedHashSet<>();
                guard.addAll(rule.getConstraints());
                for (Constraint c : inlineRule.getConstraints()) {
                    TRSFunctionApplication cterm = c.getConstraintTerm().applySubstitution(subs);
                    try {
                        guard.add(Constraint.create(cterm));
                    } catch (NoConstraintTermException e) {
                        throw new RuntimeException(); //internal error
                    }
                }

                //avoid adding unsat rules
                if (SMTHelper.isUnsat(guard, SMT_TIMEOUT, this.aborter)) {
                    continue;
                }

                TRSTerm inlineCostTerm = inlineRule.getCost().toTerm().applySubstitution(subs);
                SimplePolynomial inlineCost = TermHelper.termToCost(this.rnts, inlineCostTerm);
                SimplePolynomial cost = rule.getCost().plus(inlineCost);
                res.add(RntsRule.createUnsafe(rule.getLeft(), rhs, cost, ImmutableCreator.create(guard)));
            }
            return res;
        }

        private Set<RntsRule> inlineAll(FunctionSymbol fun, RntsRule rule) {
            Set<RntsRule> done = new LinkedHashSet<>();
            Set<RntsRule> todo = new LinkedHashSet<>();
            todo.add(rule);
            while (!todo.isEmpty()) {
                Set<RntsRule> newTodo = new LinkedHashSet<>();
                for (RntsRule todoRule : todo) {
                    Optional<Position> optpos = findInnermostInlinableFun(fun, todoRule.getRight());
                    if (!optpos.isPresent()) {
                        done.add(todoRule);
                    } else {
                        newTodo.addAll(inlineAtPos(fun, optpos.get(), todoRule));
                    }
                }
                todo = newTodo;
            }
            //special case: done is empty, as no inlining is possible (always UNSAT)
            //as there might be other positions that can be rewritten, we have to keep the rule
            if (done.isEmpty()) {
                done.add(rule);
            }
            return done;
        }

        private boolean isTerminating(FunctionSymbol fun, Set<RntsRule> rules) {
            for (RntsRule rule : rules) {
                if (rule.getRootSymbol().equals(fun)) {
                    if (!rnts.isTerminating(rule)) {
                        return false;
                    }
                }
            }
            return true;
        }

        public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
                throws AbortionException {
            Set<RntsRule> inlinedRules = new LinkedHashSet<>();
            this.aborter = aborter;
            this.rnts = (CpxRntsProblem) obl;
            Set<FunctionSymbol> done = new LinkedHashSet<>();
            Set<RntsRule> rules = new LinkedHashSet<>();
            rules.addAll(rnts.getRules());

            while (true) {
                //find candidates
                Set<FunctionSymbol> todo = new LinkedHashSet<>();
                for (FunctionSymbol fun : rnts.getDefinedSymbols()) {
                    if (!done.contains(fun) && isTerminating(fun,rules)) {
                        todo.add(fun);
                    }
                }

                if (todo.isEmpty()) {
                    break;
                }
                for (FunctionSymbol inlineFun : todo) {
                    int n = rnts.getRulesFrom(inlineFun).size();
                    Set<RntsRule> removeRules = new LinkedHashSet<>();
                    Set<RntsRule> addRules = new LinkedHashSet<>();
                    for (RntsRule rule : rules) {
                        int k = TermHelper.countFun(inlineFun, rule.getRight());
                        if (k > 0 && k * n <= MAX_RULE_BLOWUP) {
                            removeRules.add(rule);
                            addRules.addAll(inlineAll(inlineFun, rule));
                            inlinedRules.addAll(this.rnts.getRulesFrom(inlineFun));
                        }
                    }
                    done.add(inlineFun);
                    rules.removeAll(removeRules);
                    rules.addAll(addRules);
                }
            }

            if (inlinedRules.isEmpty()) {
                return ResultFactory.unsuccessful();
            }

            CpxRntsProblem newObl = rnts.cloneWithNewRules(ImmutableCreator.create(rules));
            return ResultFactory.proved(newObl, UpperBound.create(), new InliningProof(inlinedRules));
        }
    }

    private static class InliningProof extends CpxProof {
        Set<RntsRule> inlinedRules = new LinkedHashSet<>();

        public InliningProof(Set<RntsRule> r) {
            this.inlinedRules = r;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append(o.escape("Inlined the following terminating rules on right-hand sides where appropriate:"));
            s.append(o.linebreak());
            s.append(o.set(this.inlinedRules, Export_Util.RULES));
            return s.toString();
        }
    }
}
