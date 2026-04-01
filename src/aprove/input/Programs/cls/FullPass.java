/*
 * created on 26.09.2004 In this class all the inforamtion of the given input
 * are collected. Since FullPass works on a tree structure it is written
 * recursively in a depth first manner. The sets for the different rules, pairs
 * and equation are not initialzed in the constructor because of a test in the
 * ObligationCreator class, which will be executed after FullPass has been
 * successful. In ObligationCreator it is tested if a parameter like simpleRules
 * equals null, in order to decide if simple Rules have occured in the TRS.
 * Therefore the sets are not initialized until the out-Method of the apropriate
 * node, for example the outASimpleRule method is visited for the first time.
 * This has the advantage that empty sets in the TRS can be recognised and more
 * invalid combinations of rules, pairs, equations and flags can be found by
 * ObligationCreator.
 */

/**
 * @author patwie
 * @version $Id$
 */

package aprove.input.Programs.cls;

import java.util.*;
import java.util.logging.*;

import aprove.input.Generated.cls.analysis.*;
import aprove.input.Generated.cls.node.*;
import aprove.input.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class FullPass extends DepthFirstAdapter {

    protected static Logger logger = Logger.getLogger("aprove.input.Programs.trs.FullPass");

    private final Stack<String> idStack;
    private final MarkedStack<TRSTerm> termStack;
    private final MarkedStack<Rule> tempSimpleRuleStack;
    private final MarkedStack<GeneralizedRule> tempGeneralizedRuleStack;
    private final MarkedStack<ConditionalRule> tempConditionalRuleStack;
    private Set<Rule> simpleRules;
    private Set<GeneralizedRule> generalizedRules;
    private Set<ConditionalRule> conditionalRules;
    private Set<ConditionalRule> generalizedConditionalRules;
    private Set<TRSFunctionApplication> initialTerms;
    private final ParseErrors parseErrors;

    /**
     * Creates a new tree walker
     */
    public FullPass() {
        this.parseErrors = new ParseErrors();
        this.idStack = new Stack<String>();
        this.termStack = new MarkedStack<TRSTerm>();
        this.tempSimpleRuleStack = new MarkedStack<Rule>();
        this.tempGeneralizedRuleStack = new MarkedStack<GeneralizedRule>();
        this.tempConditionalRuleStack = new MarkedStack<ConditionalRule>();
    }// FullPass

    public ParseErrors getErrors(){
        return this.parseErrors;
    }

    /*
     * //TODO delete this method after testing!
     * @Override public void outStart(Start node) {
     * //System.err.print("\nTerm Stack nach Baumdurchlauf:");
     * //System.err.println(this.termStack);
     * //System.err.print("\nSimple Rule Stack nach Baumdurchlauf:");
     * //System.err.println(this.simpleRuleStack);
     * //System.err.print("\nRelative Rule Stack nach Baumdurchlauf:");
     * //System.err.println(this.relativeRuleStack);
     * System.err.println("\nTriple Rules nach Baumdurchlauf:");
     * System.err.print("\nSimple Rules: ");
     * System.err.println(this.rulesTriple.getX().toString());
     * System.err.print("\nRelative Rules: ");
     * System.err.println(this.rulesTriple.getY().toString());
     * System.err.println("\nConditional Rules:");
     * System.err.println(this.rulesTriple.getZ().toString() + "\n");
     * System.err.print("\nQ Term Set nach Baumdurchlauf:");
     * System.err.println(this.qTerms);
     * System.err.print("\nPairs Set nach Baumdurchlauf:");
     * System.err.println(this.pairs);
     * System.err.print("\nContext Sensitive Stack nach Baumdurchlauf:");
     * System.err.println(this.contextSensStack);
     * System.err.println("\nStrategy Innermost: " + this.innermost); //
     * System.err.println("\n"); } /* The method checks the two variable
     * conditions for rules in a TRS, left hand side is not a variable and all
     * variables on right hand side are also on lhs
     */
    private boolean varConditionCheck ( final TRSTerm lhs, final TRSTerm rhs){

        boolean correctRule = true;
        // if it is a lhs of a rule it can not be a variable
        if(!(lhs instanceof TRSFunctionApplication)){
            correctRule = false;
        }
        //Check the lhs/rhs variable condition
        final Set<TRSVariable> lhsVars = lhs.getVariables();
        final Set<TRSVariable> rhsVars = rhs.getVariables();
        // check if every variable on the rhs is contained in the lhs
        if(!lhsVars.containsAll(rhsVars)) {
            correctRule = false;
        }//if
        return correctRule;
    }

    @Override
    public void inARulesdeclDecl(final ARulesdeclDecl node) {
        // the three marks are necessary to avoid empty stack exceptions
        this.tempSimpleRuleStack.pushMark();
        this.tempGeneralizedRuleStack.pushMark();
        this.tempConditionalRuleStack.pushMark();
    }

    @Override
    public void outARulesdeclDecl(final ARulesdeclDecl node) {
        //empty the three temporarily rules stacks and save the information in Sets
        if(this.simpleRules!=null) {
            this.simpleRules.addAll(this.tempSimpleRuleStack.popDownToMark());
        }
        else {
            this.tempSimpleRuleStack.popDownToMark(); //only to delete the mark
        }
        if(this.generalizedRules!=null) {
            this.generalizedRules.addAll(this.tempGeneralizedRuleStack.popDownToMark());
        }
        else {
            this.tempGeneralizedRuleStack.popDownToMark(); //only to delete the mark
        }
        if(this.conditionalRules!=null) {
            for (final ConditionalRule condRule : this.tempConditionalRuleStack
                    .popDownToMark()) {
                if (condRule.isDeterministic3CTRS()) {
                    this.conditionalRules.add(condRule);
                } else {
                    if (this.generalizedConditionalRules == null) {
                        this.generalizedConditionalRules = new LinkedHashSet<ConditionalRule>(
                                1);
                    }
                    this.generalizedConditionalRules.add(condRule);
                }
            }
        }
        else {
            this.tempConditionalRuleStack.popDownToMark(); //only to delete the mark
        }

    }

    // Put the name of the constant or variable on the idStack
    // to be able to create a constant or variable out of it
    // when leaving this node with the out-Method below.
    @Override
    public void inAConstVarTerm(final AConstVarTerm node) {
        this.idStack.push(node.getId().getText().trim());
    }

    // Put the name of the constant or variable on the idStack
    // to be able to create a constant or variable out of it
    // when leaving this node with the out-Method below.
    @Override
    public void inASpecVarTerm(final ASpecVarTerm node) {
        this.idStack.push(node.getVar().getText().trim());
    }


    @Override
    public void outAConstVarTerm(final AConstVarTerm node) {
        final String s = this.idStack.pop();
        final TRSVariable v = TRSTerm.createVariable(s);
        if(s.startsWith("sv")) {
            this.termStack.push(v);
        }
        else{
            final FunctionSymbol fs = FunctionSymbol.create(s,0);
            this.termStack.push(TRSTerm.createFunctionApplication(fs, TRSTerm.EMPTY_ARGS));
        }
    }

    @Override
    public void outASpecVarTerm(final ASpecVarTerm node) {
        final String s = this.idStack.pop();
        final TRSVariable v = TRSTerm.createVariable(s);
        if(s.startsWith("sv")) {
            this.termStack.push(v);
        }
        else{
            final FunctionSymbol fs = FunctionSymbol.create(s,0);
            this.termStack.push(TRSTerm.createFunctionApplication(fs, TRSTerm.EMPTY_ARGS));
        }
    }

    // When going into a function node, put the name of the function on the idStack.
    // The termStack gets a mark, so that we know how many arguments this function
    // symbol has.
    @Override
    public void inAFunctAppTerm(final AFunctAppTerm node){
        this.termStack.pushMark();
        this.idStack.push(node.getId().getText().trim());
    }

    // The idStack has on top the name of the function symbol and on the
    // termStack are
    // exactly the arguments to this function symbol.
    @Override
    public void outAFunctAppTerm(final AFunctAppTerm node){
        final String topId = this.idStack.pop();
        final List<TRSTerm> arguments = this.termStack.popDownToMark();
        final TRSVariable var =  TRSTerm.createVariable(topId);
        // If the name of the function symbol is declared in the set of variables
        // and it has arguments an error is generated. In order to go on with the pass
        // the function symbol is pushed as a variable on the termStack to avoid
        // empty stack exceptions in the rest of the pass.
        if (topId.startsWith("sv")){
            if(!arguments.isEmpty()){
                final ParseError pe = new ParseError(ParseError.ERROR);
                final int inLine = node.getOpen().getLine();
                final int inPos = node.getOpen().getPos();
                pe.setMessage("Variable Application Error for Variable "
                        + topId + " applied to " + arguments.toString()
                        + " in line " + inLine +
                        " at position " + inPos + ", this may cause further variable errors! ");
                this.parseErrors.add(pe);
            }
            this.termStack.push(var);
        }
        else{
            final ImmutableArrayList<TRSTerm> argArrayList = ImmutableCreator.create(new ArrayList<TRSTerm>(arguments));
            final FunctionSymbol fs = FunctionSymbol.create(topId, arguments.size());
            this.termStack.push(TRSTerm.createFunctionApplication(fs, argArrayList));
        }
    }

    @Override
    public void outASimpleRule(final ASimpleRule node) {

        if(this.simpleRules==null) {
            this.simpleRules = new LinkedHashSet<Rule>();
        }

        final TRSTerm rhs = this.termStack.pop();
        final TRSTerm lhs = this.termStack.pop();

        if(this.varConditionCheck(lhs, rhs)){
            TRSFunctionApplication fa = null;
            fa = (TRSFunctionApplication) lhs;
            this.tempSimpleRuleStack.push(Rule.create(fa, rhs));
        }
        else{
            // if it has to be a lhs of a rule it can not be a variable
            if( !(lhs instanceof TRSFunctionApplication)){
                final ParseError pe1 = new ParseError(ParseError.ERROR);
                pe1.setMessage("The term " + lhs + " on the lhs of the simple rule " + lhs + " -> " + rhs + " in Rules is a variable.");
                this.parseErrors.add(pe1);
            } else {
                final GeneralizedRule rule = GeneralizedRule.create((TRSFunctionApplication) lhs, rhs);
                if (this.generalizedRules == null) {
                    this.generalizedRules = new LinkedHashSet<GeneralizedRule>();
                }
                this.tempGeneralizedRuleStack.push(rule);
            }

            /*
             * //Check the lhs/rhs variable condition Set<Variable> lhsVars =
             * lhs.getVariables(); Set<Variable> rhsVars = rhs.getVariables();
             * // check if every variable on the rhs is contained in the lhs
             * for(Variable vRhs : rhsVars) { if(!lhsVars.contains(vRhs)) { //
             * not allowed -> exit with error ParseError pe = new
             * ParseError(ParseError.ERROR);
             * pe.setMessage("The rhs of the simple rule " + lhs + " -> " + rhs
             * + " in Rules contains the variable " + vRhs +
             * " which does not occur on the lhs."); this.parseErrors.add(pe);
             * }//if }//for
             */
        }//else
    }

    @Override
    public void outAInitialdeclDecl(final AInitialdeclDecl node) {
        if (this.initialTerms == null) {
            this.initialTerms = new LinkedHashSet<TRSFunctionApplication>();
        }

        while (this.termStack.isNotEmpty()) {
            final TRSTerm tempTerm = this.termStack.pop();
            if (tempTerm instanceof TRSVariable) {
                final ParseError pe = new ParseError(ParseError.ERROR);
                pe.setMessage("In the set of INITAL only Function Applications are allowed, no standalone Variables.");
                this.parseErrors.add(pe);
            } else {
                final TRSFunctionApplication fa = (TRSFunctionApplication) tempTerm;
                this.initialTerms.add(fa);
            }
        }
    }

    @Override
    public void outAPoorCond(final APoorCond node) {
        TRSFunctionApplication cond = (TRSFunctionApplication) this.termStack.pop();
        assert(cond.getRootSymbol().getName().equals("1") && cond.getRootSymbol().getArity() == 0);
    }

    @Override
    public void outAConditionalRule(final AConditionalRule node) {
        if(this.conditionalRules==null) {
            this.conditionalRules = new LinkedHashSet<ConditionalRule>();
        }

        /*
         * At this point all the pieces of information needed to build the
         * Conditional rule are on the term Stack and are transferred into a
         * list of conditions. The way the stack is built, we can assure that
         * the two terms at the bottom are the terms of the simple rule,
         * anything above is a condition.
         */
        //Read out the condition List
        final List<Condition> conditionList = new LinkedList<Condition>();

        while(this.termStack.size() > 2){
            final TRSTerm tempCondright = this.termStack.pop();
            final TRSTerm tempCondleft = this.termStack.pop();
            final Condition tempCondition = Condition.create(tempCondleft, tempCondright, Condition.ConditionType.ARROW);
            conditionList.add(0, tempCondition);
        }//while
        final ImmutableList<Condition> immutableConditionList = ImmutableCreator.create(conditionList);

        /*
         * the remaining two terms on the stack are the rhs and lhs of the
         * simple Rule First build a rule out of these two terms then call the
         * ConditionalRule create method
         */

        final TRSTerm rhs = this.termStack.pop();
        final TRSTerm lhs = this.termStack.pop();
        GeneralizedRule simpleRule; // to store the simple Rule part of the conditional
        // Rule

        final TRSFunctionApplication fa = (TRSFunctionApplication) lhs;
        simpleRule = GeneralizedRule.create(fa, rhs);
        final ConditionalRule condRule = ConditionalRule.create(simpleRule, immutableConditionList);
        if(true || condRule.isDeterministic3CTRS()){
            this.tempConditionalRuleStack.push(condRule);
        }
        else{
            // if it has to be a lhs of a rule it can not be a variable
            if( !(lhs instanceof TRSFunctionApplication)){
                final ParseError pe1 = new ParseError(ParseError.ERROR);
                pe1.setMessage("The term " + lhs + " on the lhs of the simple rule " + lhs + " -> " + rhs + " in Conditional Rules is a variable.");
                this.parseErrors.add(pe1);
            }
            //Check the lhs/rhs variable condition
            final Set<TRSVariable> vars = lhs.getVariables();
            for (final Condition cond : immutableConditionList) {
                for (final TRSVariable v : cond.getLeft().getVariables()) {
                    if (!vars.contains(v)) {
                        final ParseError pe = new ParseError(ParseError.ERROR);
                        pe.setMessage("The condition '"+cond+"' of the conditional rule " + lhs + " -> " + rhs + " in Conditional Rules contains the variable " + v + " which does not occur on the lhs or on the rhs of a previous condition.");
                        this.parseErrors.add(pe);
                    }
                }
                vars.addAll(cond.getRight().getVariables());
            }
            for (final TRSVariable v : rhs.getVariables()) {
                if (!vars.contains(v)) {
                    final ParseError pe = new ParseError(ParseError.ERROR);
                    pe.setMessage("The rhs of the conditional rule " + lhs + " -> " + rhs + " in Conditional Rules contains the variable " + v + " which does not occur on the lhs or on the rhs of a previous condition.");
                    this.parseErrors.add(pe);
                }
            }
        }//else
    }

    public Set<Rule> getSimpleRules(){
        return this.simpleRules;
    }

    public Set<GeneralizedRule> getGeneralizedRules(){
        return this.generalizedRules;
    }

    public Set<ConditionalRule> getConditionalRules(){
        return this.conditionalRules;
    }

    public Set<ConditionalRule> getGeneralizedConditionalRules(){
        return this.generalizedConditionalRules;
    }

    public Set<TRSFunctionApplication> getInitialTerms() {
        return this.initialTerms;
    }

}//FullPass
