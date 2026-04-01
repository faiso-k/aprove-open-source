package aprove.input.Programs.fp;


import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.Predef.IntegerPredef.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.*;



/**
 * Helper to make the rules of a defining FunctionSymbol non-overlapping.
 * Here, it is assumed that the rules are left-linear and constructor-based, i.e. all arguments are built from constructors and variables.
 */
public class PatternDisjunctor {


    private static Vector<Vector<Rule>> ifBlocks;
    private static Vector<Rule> curRulesVec;
    private static Vector<Rule> conRulesVec;


    private static Logger logger = Logger.getLogger("aprove.input.Programs.fp.PatternDisjunctor");

    private static boolean containsInts;

    /** creates from a set of rules of one defining FunctionSymbol a set of rules
     * for which the left hand sides are non-overlapping
     * it is necessary that all rules for the defined symbol are in the parameter rules
     * and conditional rules must be of such a form, that rules which overlap have the same conditions
     * NOTE: there is no copying, therefore the parameter set should not be used anymore
     * @param rules Rules for one FunctionSymbol, in the order they appear in the program
     * @param typeContext Type context that defines the types for the terms used
     * @param containsInts Indication whether the type context contains integers that need special treatment (e.g. no succ inside a pred)
     * @return a new set of rules, in which the left hand sides have disjunct patterns
     */
    public static LinkedHashSet<Rule> makePatternsNonOverlapping(LinkedHashSet<Rule> rules, TypeContext typeContext, boolean containsInts) {
        if ( (rules == null) || (rules.isEmpty()) || (rules.size() == 1) ) {
            return rules;
        }

        PatternDisjunctor.containsInts = containsInts;

        if (aprove.Globals.useAssertions) {
            Symbol sym = rules.iterator().next().getLeft().getSymbol();
            assert (sym instanceof DefFunctionSymbol) : "Symbol "+sym+" is not a defined function!";

            for(Rule r : rules) {
                assert (r.getLeft().getSymbol().equals(sym)) : "rule "+r+" is not for the expected defined function "+sym;
            }
        }

        // the rules with an index, used to decide which rule is standing in front of the other in case of a conflict
        RulesIndexed rulesWithIndex = new RulesIndexed(rules);

        // building the structure storing what rules were built from the same if-then-else statement
        PatternDisjunctor.buildIfBlocks(rules);

        boolean changed = true;
        while(changed) {
            changed = false;
            // the left hand sides before this one
            List<Rule> prevRules = new Vector<Rule>();
            for(Rule currentRule : rulesWithIndex.keySet()) {
                AlgebraTerm left = currentRule.getLeft();
                Rule conflictingRule = null;
                int conflictingRuleIndex = 0;
                for(Rule prevRule : prevRules) {
                    // if both left hand sides are the same object, they must have different conditions by construction. Hence try the next rule
                    if (prevRule.getLeft() == currentRule.getLeft()) {
                        continue;
                    }

                    conflictingRuleIndex = rulesWithIndex.get(prevRule);
                    FreshVarGenerator fvg = new FreshVarGenerator(left);
                    Rule prevRuleRenamed = prevRule.replaceVariables(fvg);
                    if (prevRuleRenamed.getLeft().isUnifiable(left) && !PatternDisjunctor.sameIfBlock(left, prevRule.getLeft())) {
                        // In this case we have an overlap
                        conflictingRule = prevRuleRenamed;
                        break; // stops the iteration over the prevRules
                    }
                }

                if (conflictingRule != null) {
                    PatternDisjunctor.processConflict(rulesWithIndex, currentRule, conflictingRule, conflictingRuleIndex, typeContext);
                    changed = true; // even if no rules were added, there still is a change since currentRule was removed
                    break; // stops the iteration over the rules; the (implicit) iterators need to be reinitialized
                }

                prevRules.add(currentRule);
            }
        }

        return rulesWithIndex.toLinkedSet();
    }



    /**
     * builds up the vectors which contain the rules that originated from one if-then-else statement
     * this is found out, by looking at the left hand sides: if for two rules the left hand sides are the same object,
     * then this must be the case
     * @param rules a set of rules where for conditional rules the same lhs is used if they belong to the same if-then-else statement
     */
    private static void buildIfBlocks(Set<Rule> rules) {
        PatternDisjunctor.ifBlocks = new Vector<Vector<Rule>>();
        for (Rule rule : rules) {
            if (rule.getConds().size() == 0) {
                continue;
            }
            boolean ruleAdded = false;
            for (Vector<Rule> vecRules : PatternDisjunctor.ifBlocks) {
                for (Rule r : vecRules) {
                    if (rule.getLeft() == r.getLeft()) {
                        vecRules.add(rule);
                        ruleAdded = true;
                        break;
                    }
                }
                if (ruleAdded) {
                    break;
                }
            }
            if (!ruleAdded) {
                PatternDisjunctor.ifBlocks.add(new Vector<Rule>(Arrays.asList(rule)));
            }
        }
    }



    /**
     * checks whether two left hand sides originated to the same if-then-else statement
     * on the fly the pointer to the vectors that contain the rules for the if-then-else statements for two left hand sides
     * @param curRuleLeft a left hand side of a rule
     * @param prevRuleLeft another left hand side of a rule
     * @return true iff both terms belong to rules that originated from the same if-then-else statement
     */
    private static boolean sameIfBlock(AlgebraTerm curRuleLeft, AlgebraTerm prevRuleLeft) {
        PatternDisjunctor.curRulesVec = null;
        PatternDisjunctor.conRulesVec = null;
        for (Vector<Rule> vecRules : PatternDisjunctor.ifBlocks) {
            boolean found1 = false;
            boolean found2 = false;
            for (Rule r : vecRules) {
                if (r.getLeft() == curRuleLeft) {
                    found1 = true;
                    PatternDisjunctor.curRulesVec = vecRules;
                }
                if (r.getLeft() == prevRuleLeft) {
                    found2 = true;
                    PatternDisjunctor.conRulesVec = vecRules;
                }
                if (found1 && found2) {
                    return true;
                }
            }
        }
        return false;
    }



    /**
     * updates the if-then-else statement's rule list
     * this relys that previously sameIfBlockRules was called and since the right rules are referenced by curRulesVec
     */
    private static void updateIfBlockRules(Set<Rule> newRules) {
        if (PatternDisjunctor.curRulesVec != null) {
            PatternDisjunctor.curRulesVec.addAll(newRules);
        }
    }





    /** takes a conflicting pair of rules, removes the one that occurs under the other in the program
     * and adds all cases that were covered by the removed rule but not by the conflictingRule
     * @param rulesWithIndex set of rules with indices indicating the position
     * @param currentRule a conflicting rule
     * @param conflictingRule the other conflicting rule, it is assumed that in this rule the variables have been renamed
     * @param conflictingRuleIndex the index of the conflicting rule (needed, because of the variable renaming it cannot be determined)
     * @param typeContext TypeContext for the involved types
     */
    private static void processConflict(RulesIndexed rulesWithIndex, Rule currentRule, Rule conflictingRule, int conflictingRuleIndex, TypeContext typeContext) {
        AlgebraTerm left = currentRule.getLeft();

        // if the conflictingRule has a higher index, then the currentRule should define the covered patterns => switch both rules
        int ruleIndex = rulesWithIndex.get(currentRule);
        if (conflictingRuleIndex > ruleIndex) {

            // XXX DEBUG
            PatternDisjunctor.logger.finer("switching: ruleIndex "+ruleIndex+" with conflictingRuleIndex "+conflictingRuleIndex+"\n");

            Rule temp = conflictingRule;            int tempIndex = conflictingRuleIndex;
            conflictingRule = currentRule;            conflictingRuleIndex = ruleIndex;
            currentRule = temp;                        ruleIndex = tempIndex;
            left = currentRule.getLeft();

            PatternDisjunctor.curRulesVec = PatternDisjunctor.conRulesVec;
        }

        // removing the currentRule that has an overlap with the conflictingRule
        rulesWithIndex.remove(currentRule);

        // add the rules that are missing after removal of currentRule, where the patterns do not overlap with conflictingRule anymore
        try {
            AlgebraTerm conflictingLeft = conflictingRule.getLeft();

            AlgebraSubstitution mgu = left.unifies(conflictingLeft);

            // XXX DEBUG
            PatternDisjunctor.logger.finer("Conflict (mgu="+mgu+"):\n");
            PatternDisjunctor.logger.finer("\t"+currentRule+"/"+ruleIndex+" vs. "+conflictingRule+"/"+conflictingRuleIndex+" varren: "+mgu.isVariableRenaming()+"\n");

            // if the unification is just a variable-renaming, then only the conflictingRule is retained (newRules will be empty)
            LinkedHashSet<Rule> newRules = PatternDisjunctor.resolveOverlap(currentRule, conflictingLeft, typeContext);
            rulesWithIndex.addAll(newRules,ruleIndex);

            // update the if-block information
            PatternDisjunctor.updateIfBlockRules(newRules);

            // XXX DEBUG
            PatternDisjunctor.logger.finer("\tnew rules:"+"\n");
            for(Rule rule : newRules) {
                PatternDisjunctor.logger.finer("\t\t"+rule+"\n");
            }

        } catch (UnificationException e) {
            throw new RuntimeException("Tried to resolve conflict on non-unifiable left hand sides.");
        }
    }




    /** resolves an overlap between a rule and another left hand side
     * it is assumed that rule.getLeft() and conflictingLeft match and have different variable names
     * @param rule rule for which the conflict occured
     * @param conflictingLeft the left hand side that unifies rule.getLeft()
     * @param typeContext TypeContext which defines the constructor symbols
     * @return a rule to be used instead of the original rule
     */
    private static LinkedHashSet<Rule> resolveOverlap(Rule rule, AlgebraTerm conflictingLeft, TypeContext typeContext) {
        AlgebraTerm left = rule.getLeft();

        if (aprove.Globals.useAssertions) {
            assert new HashSet<VariableSymbol>(left.getVariableSymbols()).removeAll(conflictingLeft.getVariableSymbols()) == false : "Terms "+left+" and "+conflictingLeft+" have common variables.";
        }

        // getting the mgu between left and conflictingLeft
        AlgebraSubstitution tau;
        try {
            tau = left.unifies(conflictingLeft);
        } catch (UnificationException e) {
            throw new RuntimeException("resolveOverlap was called with non-unifiable terms "+left+" and "+conflictingLeft);
        }

        LinkedHashSet<Rule> nonOverlappingRules = new LinkedHashSet<Rule>();
        FreshVarGenerator fvg = new FreshVarGenerator(left);
        for(VariableSymbol varSym : tau.getDomain()) {

            // for renamed variables nothing has to be done
            if(tau.get(varSym).isVariable()) {
                continue;
            }

            // this position is needed to determine the set of non-allowed symbols at this position (e.g. no pred inside a succ allowed)
            Set<Position> positions = left.getPositionsWithSymbol(varSym);

            // the varSym comes from the term conflictingLeft => no change in rule for this variable
            if (positions.isEmpty()) {
                continue;
            }

            if (aprove.Globals.useAssertions) {
                // here the size can only be >= 1
                assert positions.size() == 1 : "Non left-linear term encountered: "+left;
            }

            Position pi = positions.iterator().next();
            int argNum = pi.getLast();
            Position piPrime = pi.pred();

            // it does not matter from where fsym is taken since both must be equal; otherwise there would not be a unificator tau
            Symbol fsym = left.getSubterm(piPrime).getSymbol();
            AlgebraTerm fsymArgType = TypeTools.getFunctionArgAt(typeContext.getSingleTypeOf(fsym).getTypeMatrix(), argNum);
            Set<Symbol> disallowedSymbols = PatternDisjunctor.getDisallowedSymbols(fsym, typeContext);

            // terms different from this one
            for(AlgebraTerm nonOvTerm : PatternDisjunctor.computeNonOverlappingTerms(tau.get(varSym), fsymArgType, disallowedSymbols, fvg, typeContext)) {
                AlgebraSubstitution sigma = AlgebraSubstitution.create();
                sigma.put(varSym, nonOvTerm);
                Rule newRule = rule.deepcopy().apply(sigma);
                nonOverlappingRules.add(newRule);
            }

            // if there still are replacements inside the unficator tau, that are not variable renamings, these have to be considered on the rule
            // where the previous replacements of tau have been made; therefore add the current replacement
            AlgebraSubstitution sigma = AlgebraSubstitution.create();
            sigma.put(varSym, tau.get(varSym));
            rule = rule.deepcopy().apply(sigma);
            left = rule.getLeft();
        }

        return nonOverlappingRules;
       }


    /** computes recursively the terms that are non-overlapping with conflictingLeft
     * @param conflictingLeft Term the lhs conflicts with
     * @param leftArgType Type of conflictingLeft and thus also of the lhs
     * @param disallowedSymbols Constructors that are not allowed inside this argument (e.g. for integers, it is not allowed to have a pred inside a succ)
     * @param fvg FreshVarGenerator that contains the used names of the lhs
     * @param typeContext Current TypeContext
     * @return Set of terms that are the cases not covered by conflictingLeftArg
     */
    private static Set<AlgebraTerm> computeNonOverlappingTerms(AlgebraTerm conflictingLeft, AlgebraTerm leftArgType, Set<Symbol> disallowedSymbols, FreshVarGenerator fvg, TypeContext typeContext) {
        Set<AlgebraTerm> missingTerms = new HashSet<AlgebraTerm>();

        if (conflictingLeft.isVariable()) {
            // in this case there are no more terms missing, since the variable will match them
            return missingTerms;
        }

        Set<ConstructorSymbol> consSyms = new HashSet<ConstructorSymbol>();
        ConstructorSymbol typeConstructorSym = (ConstructorSymbol)leftArgType.getSymbol();
        for(Symbol cons : typeContext.getTypeDefOf(typeConstructorSym).getDeclaredSymbols()) {
            if (!disallowedSymbols.contains(cons)) {
                consSyms.add((ConstructorSymbol)cons);
            }
        }

        if (aprove.Globals.useAssertions) {
            assert conflictingLeft.getSymbol() instanceof ConstructorSymbol : "The term "+conflictingLeft+" does not start with a constructor symbol.";
        }

        ConstructorSymbol usedConsSym = (ConstructorSymbol)conflictingLeft.getSymbol();

        for(ConstructorSymbol consSym : consSyms) {
            if (!consSym.equals(usedConsSym)) {
                List<AlgebraTerm> consArgs = new Vector<AlgebraTerm>(consSym.getArity());
                for(int i=0;i<consSym.getArity(); ++i) {
                    consArgs.add(fvg.getFreshVariable("x_"+(i+1),consSym.getArgSort(i),false));
                }
                AlgebraTerm consTerm = AlgebraFunctionApplication.create(consSym, consArgs);
                missingTerms.add(consTerm);
            }
            else {
                AlgebraTerm consTypeM = typeContext.getSingleTypeOf(consSym).getTypeMatrix();
                Set<List<AlgebraTerm>> argumentLists = new HashSet<List<AlgebraTerm>>();
                for(int i=0;i<consSym.getArity();++i) {

                    AlgebraTerm conflictingLeftArg = conflictingLeft.getArgument(i);
                    AlgebraTerm conflictingLeftArgType = TypeTools.getFunctionArgAt(consTypeM,i);
                    Set<Symbol> argDisallowedSymbols = PatternDisjunctor.getDisallowedSymbols(usedConsSym,typeContext);

                    Set<AlgebraTerm> missingArgs = PatternDisjunctor.computeNonOverlappingTerms(conflictingLeftArg,conflictingLeftArgType,argDisallowedSymbols,fvg,typeContext);
                    // if there is nothing missing, insert a fresh variable
                    if (missingArgs.isEmpty()) {
                        missingArgs.add(fvg.getFreshVariable("x_"+(i+1),consSym.getArgSort(i),false));
                    }
                    for(AlgebraTerm arg : missingArgs) {
                        if (i==0) {
                            List<AlgebraTerm> argList = new Vector<AlgebraTerm>();
                            argList.add(arg);
                            argumentLists.add(argList);
                        }
                        else {
                            for(List<AlgebraTerm> argList : argumentLists) {
                                argList.add(arg);
                            }
                        }
                    }
                }

                for(List<AlgebraTerm> argList : argumentLists) {
                    boolean onlyVars = true;
                    for(AlgebraTerm arg : argList) {
                        onlyVars = onlyVars & arg.isVariable();
                    }
                    if (!onlyVars) {
                        AlgebraTerm consTerm = AlgebraFunctionApplication.create(consSym, argList);
                        missingTerms.add(consTerm);
                    }
                }
            }
        }

        return missingTerms;
    }



    private static Set<Symbol> getDisallowedSymbols(Symbol sym, TypeContext typeContext) {
        Set<Symbol> disallowedSymbols;
        if (PatternDisjunctor.containsInts && IntegerTools.isIntSymbol(sym,typeContext)) {
            disallowedSymbols = IntegerTools.getDisallowedSymbols(sym, typeContext);
        }
        else {
            disallowedSymbols = new HashSet<Symbol>();
        }

        return disallowedSymbols;
    }




    /** class that keeps a set of rules and their position in a predictable order.
     */
    private static class RulesIndexed extends LinkedHashMap<Rule,Integer> {

        /** creates a new Map with pairs rule->int where int is the position in the set
         * only those rules are added that were not in the map before
         * @param rules Rules to add
         */
        public RulesIndexed(LinkedHashSet<Rule> rules) {
            int i=1;
            for(Rule rule : rules) {
                if(this.add(rule,i)) {
                    ++i;
                }
            }
        }


        /** creates a map where the references are copied from rules
         * @param rules RulesIndexed from which the references shall be copieds
         */
        public RulesIndexed(RulesIndexed rules) {
            for(Map.Entry<? extends Rule, ? extends Integer> entry : rules.entrySet()) {
                this.add(entry.getKey(), entry.getValue());
            }
        }


        /** adds a new rule->int pair, if the rule was not in the map before or if the new index is smaller than the old one
         * @param r A rule
         * @param index An integer
         * @return true if the pair was added
         */
        public boolean add(Rule r, Integer index) {
            Integer oldIndex = this.get(r);
            if ( (oldIndex != null) && (oldIndex.intValue() < index.intValue()) ) {
                return false;
            }
            else {
                super.put(r, index);
                return true;
            }
        }

        /** adds all the rules that were not included before using add(Rule,Integer)
         * @param rules Indexed rules to add
         * @param index Index to assign to all rules
         */
        public void addAll(Set<Rule> rules, Integer index) {
            for(Rule rule : rules) {
                this.add(rule,index);
            }
        }

        /** cuts away the indices and returns the rules stored
         * @return The stored rules sorted by indices
         */
        public LinkedHashSet<Rule> toLinkedSet() {
            LinkedHashSet<Rule> rules = new LinkedHashSet<Rule>();
            int i=0;
            while (rules.size() < this.size()) {
                ++i;
                for(Map.Entry<? extends Rule, ? extends Integer> entry : this.entrySet()) {
                    if (entry.getValue().intValue()==i) {
                        rules.add(entry.getKey());
                    }
                }
            }
            return rules;
        }


        /** retrieves all numbers stored
         */
        public Set<Integer> getNumbers() {
            Set<Integer> numbers = new HashSet<Integer>();
            for(Map.Entry<? extends Rule, ? extends Integer> entry : this.entrySet()) {
                numbers.add(entry.getValue());
            }
            return numbers;
        }
    }
}
