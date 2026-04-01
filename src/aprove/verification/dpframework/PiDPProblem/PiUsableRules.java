package aprove.verification.dpframework.PiDPProblem;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;


/**
 * @author thiemann
 */
class PiUsableRules {

        /**
         * compute the (innermost) improved usable rules.
         * DO NOT CALL THIS METHOD DIRECTLY, BUT USE scc.getUsableRules()!
         * @param scc
         * @return
         */
    static ImmutableSet<GeneralizedRule> computeUsableRules(AbstractPiDPProblem pidp) {
        AbstractPiTRSProblem rWithPi = pidp.getRwithPi();
            //System.err.println("innermost usable rules not yet fully integrated, using termination usable rules");
            Set<TRSTerm> todo = new LinkedHashSet<TRSTerm>();
            for (GeneralizedRule s_to_t : pidp.getP()) {
                todo.add(s_to_t.getRight());
            }
            return PiUsableRules.used_computation(todo, rWithPi);
        }

        /**
         * calculates improved usable rules for termination
         */
        public static ImmutableSet<GeneralizedRule> used(TRSTerm t, PiDPProblem pidp) {
            Set<TRSTerm> todo = new LinkedHashSet<TRSTerm>();
            todo.add(t);
            return PiUsableRules.used_computation(todo, pidp.getRwithPi());
        }

        /**
         * creates a copy of a rule map where the sets may be modified
         * @param ruleMap
         * @return
         */
        private static Map<FunctionSymbol, Set<GeneralizedRule>> createMutableCopy(Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap) {
            Map<FunctionSymbol, Set<GeneralizedRule>> result = new LinkedHashMap<FunctionSymbol, Set<GeneralizedRule>>();
            for (Map.Entry<FunctionSymbol, ImmutableSet<GeneralizedRule>> entry : ruleMap.entrySet()) {
                result.put(entry.getKey(), new LinkedHashSet<GeneralizedRule>(entry.getValue()));
            }
            return result;
        }



        /**
         * internal method for efficient computation of improved usable rules
         * for termination.
         * Up to now, Q is not used.
         * todo: The set of terms t for that we have to add U(t) (will be modified)
         */
    private static ImmutableSet<GeneralizedRule> used_computation(Set<TRSTerm> todo,
        AbstractPiTRSProblem rWithPi) {
            // maybe: the rules that are not yet usable.
            // usable: the rules that are usable.
            Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> R = rWithPi.getRuleMap();
            Map<FunctionSymbol, Set<GeneralizedRule>> maybe = PiUsableRules.createMutableCopy(R);
            Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR = GeneralizedRule.computeLhsOfRulesAsMapInStandardRepresentation(R);
            Set<GeneralizedRule> usable = new LinkedHashSet<GeneralizedRule>();

            while (!todo.isEmpty()) {
                Iterator<TRSTerm> iter = todo.iterator();
                TRSTerm t = iter.next();
                iter.remove();
                if (t.isVariable()) {
                    continue;
                }
                TRSFunctionApplication ft = (TRSFunctionApplication) t;
                FunctionSymbol f = ft.getRootSymbol();

                // add subterms as todos
                for (TRSTerm t_i : ft.getArguments()) {
                    todo.add(t_i);
                }

                // check whether we want to add some rules
                Set<GeneralizedRule> candidates = maybe.get(f);
                if (candidates != null) {
                    // okay, we have to build f(cap(t_i)) and try unifications
                    TRSTerm ftcap = ft.tcapNe(lhsR);

                    // now check against all possible usable rule candidates
                    Iterator<GeneralizedRule> ruleIter = candidates.iterator();
                    while (ruleIter.hasNext()) {
                        GeneralizedRule candidate = ruleIter.next();
                        //@TODO better approximation using icap and finite variable set
                        if (candidate.getLhsInStandardRepresentation().unifiesRational(ftcap,new HashSet<TRSVariable>()).x) {
                            usable.add(candidate);
                            ruleIter.remove();
                            todo.add(candidate.getRight());
                        }
                    }
                    // check whether there are no f-candidates left
                    if (candidates.isEmpty()) {
                        maybe.remove(f);
                    }
                }

            }
            return ImmutableCreator.create(usable);
        }

//        /**
//         * calculates improved usable rules for innermost termination
//         */
//        private static Set<Rule> used_s(Set<Rule> P, Set<Rule> R) {
//            // note that in the innermost case we cannot merge the
//            // computation of different DPs as in the termination case.
//            // We furthermore have to start from R every time and may
//            // not proceed with the set maybe from another DP-Used_s(t) calculation
//
//            Set<Variable> vars = Rule.getVariables(R);
//            FreshVarGenerator generator = new FreshVarGenerator(vars);
//
//            // first rename all pairs in P such that no variables of R
//            // occur in P_renamed
//            Set<Rule> P_renamed = new LinkedHashSet<Rule>();
//            for (Rule s_to_t : P) {
//                s_to_t = s_to_t.replaceVariables(generator);
//                vars.addAll(s_to_t.getUsedVariables());
//                P_renamed.add(s_to_t);
//            }
//
//            // a new generator relying on vars of P_renamed and R
//            generator = new FreshVarGenerator(vars);
//
//            // now P_renamed, generator, and R fulfill the requirements
//            // of the computation algorithm.
//
//            // collect usable rules
//            Set<Rule> usable = new LinkedHashSet<Rule>();
//            Set<Term> todo = new LinkedHashSet<Term>();
//            int n = R.size();
//
//            for (Rule s_to_t : P_renamed) {
//                if (usable.size() == n) {
//                    return usable;
//                } else {
//                    todo.add(s_to_t.getRight());
//                    usable.addAll(
//                            used_s_computation(s_to_t.getLeft(), todo, R, generator)
//                            );
//                }
//            }
//
//            return usable;
//        }
//
//
//        /**
//         * calculates improved usable rules for innermost termination
//         */
//        public static Set<Rule> used_s(Rule s_to_t, Set<Rule> R) {
//            Set<Variable> vars = Rule.getVariables(R);
//            // make s -> t variable disjoint from R
//            s_to_t = s_to_t.replaceVariables(vars);
//
//            // init fresh var generator
//            vars.addAll(s_to_t.getUsedVariables());
//            FreshVarGenerator generator = new FreshVarGenerator(vars);
//
//            return used_s(s_to_t, R, generator);
//        }
//
//        /**
//         * calculates improved usable rules for innermost termination.
//         *
//         * Requirements:
//         * s -> t is renamed apart from R,
//         * Generator does not produce variables occurring in s->t or R.
//         */
//        public static Set<Rule> used_s(Rule s_to_t, Set<Rule> R, FreshVarGenerator generator) {
//            // init todo set
//            Set<Term> todo = new LinkedHashSet<Term>();
//            todo.add(s_to_t.getRight());
//            return used_s_computation(s_to_t.getLeft(), todo, R, generator);
//        }
//
//
//
//        /**
//         * internal method for efficient computation of improved usable rules
//         * for innermost termination.
//         * s: s.
//         * todo: The set of terms t for that we have to add U(t).
//         * maybe: the rules that are not yet usable.
//         * usable: the rules that are usable.
//         * generator: fresh variable generator.
//         *
//         * Requirements:
//         * - the generator does not produce variables occurring in s or R.
//         * - s does not share variables with R
//         * (Reason: Then we do not need renaming for unification)
//         */
//        private static Set<Rule> used_s_computation(Term s, Set<Term> todo, Set<Rule> R, FreshVarGenerator generator) {
//            Set<Rule> maybe = new HashSet<Rule>(R);
//            Set<Rule> usable = new HashSet<Rule>();
//
//            while (!todo.isEmpty()) {
//                Iterator<Term> iter = todo.iterator();
//                Term t = iter.next();
//                iter.remove();
//                if (t.isVariable()) continue;
//                if (t.isSubtermOf(s)) continue;
//                FunctionSymbol functionSymbol = (FunctionSymbol) t.getSymbol();
//                Vector<Term> arguments = new Vector<Term>();
//                int n = functionSymbol.getArity();
//                for (int i = 0; i < n; i++) {
//                    Term t_i = t.getArgument(i);
//                    todo.add(t_i);
//                    arguments.addElement(t_i.icap_s(s, generator, R));
//                }
//                Term ficap_s = FunctionApplication.create(functionSymbol, arguments);
//
//                // check for usability
//                Iterator<Rule> ruleIter = maybe.iterator();
//                while (ruleIter.hasNext()) {
//                    Rule rule = ruleIter.next();
//                    try {
//                        Substitution sigma = rule.getLeft().unifies(ficap_s);
//                        // unifiable, check normal condition
//                        if (s.apply(sigma).isNormal(R)) {
//                            // put rule from maybe into usable
//                            usable.add(rule);
//                            ruleIter.remove();
//                            // and add rhs to todo-list
//                            todo.add(rule.getRight().ren(generator, true));
//                        }
//                    } catch (UnificationException e) {
//                        // not unifiable
//                        continue;
//                    }
//                }
//            }
//            return usable;
//        }
//
//    }

}
