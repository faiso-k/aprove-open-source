/**
 *
 * @author Christoph Weidmann
 * @version $Id$
 */
package aprove.input.Programs.srs2;

import java.util.*;

import aprove.input.Generated.srs2.analysis.*;
import aprove.input.Generated.srs2.node.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

// This class generates terms out of the word-nodes of the abstract syntax tree,
// and, out of these terms, it generates rules.

public class SecondPass extends DepthFirstAdapter {


    private Set<String> fnames; // to store the names of the function symbols
    private TRSVariable myVar; // in SRS, we only need one variable

    private Stack<FunctionSymbol> fsStack; // to store unary function symbols
    private Stack<TRSFunctionApplication> faStack; // to store function applications

    private Set<Rule> normalRules; // to store normal rules
    private Set<Rule> relativeRules; // to store relative rules

    private boolean leftmost = false; // to store strategy information
    private boolean rightmost = false; // to store strategy information

    public SecondPass(Set<String> fsymbolNames) {
        this.fnames = fsymbolNames;
        FreshNameGenerator fng =
            new FreshNameGenerator(this.fnames, FreshNameGenerator.TYPE_INFERENCE);
        this.myVar = TRSTerm.createVariable(fng.getFreshName("x", true)); // use a fresh variable
        this.fsStack = new Stack<FunctionSymbol>();
        this.faStack = new Stack<TRSFunctionApplication>();
        this.normalRules = new LinkedHashSet<Rule>();
        this.relativeRules = new LinkedHashSet<Rule>();
        //this.parseErrors = new ParseErrors();

    }

    // When entering a OneWord-node,
    // get the name of the symbol, create a proper unary function symbol out of it
    // and put that on the fsStack.
    @Override
    public void inAOneWord(AOneWord node)
    {
        String symbolName = node.getId().getText().trim();
/*        if(Globals.DEBUG_WEIDMANN) {
            System.err.println("\nInAOneNode: " + symbolName);
          } */
        FunctionSymbol fs = FunctionSymbol.create(symbolName,1);
        this.fsStack.push(fs);

    }

    // When leaving a OneWord-Node,
    // we know that the end of one side of a rule has been reached.
    // So we get the corresponding function symbol of this node from the fsStack,
    // create a function application out of it and our only variable myVar,
    // and put this function application on the faStack.
    @Override
    public void outAOneWord(AOneWord node)
    {
        FunctionSymbol fs = this.fsStack.pop();
        List<TRSTerm> arguments = new ArrayList<TRSTerm>();
        arguments.add(this.myVar);

        ImmutableArrayList<TRSTerm> args = ImmutableCreator.create(new ArrayList<TRSTerm>(arguments));
        TRSFunctionApplication  fa = TRSTerm.createFunctionApplication(fs,args);
/*        if(Globals.DEBUG_WEIDMANN) {
          System.err.println("\nOutAOneWord: " + fa.toString());
        } */
        this.faStack.push(fa);

    }

    // When entering a MoreWord-node,
    // get the name of the symbol, create a proper unary function symbol out of it
    // and put that on the fsStack.
    @Override
    public void inAMoreWord(AMoreWord node)
    {
        String symbolName = node.getId().getText().trim();
        FunctionSymbol fs = FunctionSymbol.create(symbolName,1);
        this.fsStack.push(fs);
    }

    // When leaving a MoreWord-Node,
    // get the corresponding function symbol from fsStack,
    // create a new function application out of it with the
    // function application on the faStack as second argument,
    // and put this new function application on the faStack.
    @Override
    public void outAMoreWord(AMoreWord node)
    {
        FunctionSymbol fs = this.fsStack.pop();
        TRSFunctionApplication fa = this.faStack.pop();

        List<TRSTerm> arguments = new ArrayList<TRSTerm>();
        arguments.add(fa);

        ImmutableArrayList<TRSTerm> args = ImmutableCreator.create(new ArrayList<TRSTerm>(arguments));
        this.faStack.push(TRSTerm.createFunctionApplication(fs,args));
    }

    // When leaving a NormalRule-Node,
    // we get the rhs and lhs from the faStack
    // and create a new rule,
    // which we add to the set of normal rules
    @Override
    public void outANormalRule(ANormalRule node)
    {
        TRSFunctionApplication rhs = this.faStack.pop();
        TRSFunctionApplication lhs = this.faStack.pop();
        Rule rule = Rule.create(lhs, rhs);
        this.normalRules.add(rule);
    }

    // When leaving an EmptyRule-Node,
    // we get the lhs from the faStack,
    // use myVar as rhs,
    // and create a new rule,
    // which we add to the set of normal rules
    @Override
    public void outAEmptyRule(AEmptyRule node)
    {
        TRSFunctionApplication lhs = this.faStack.pop();
        Rule rule = Rule.create(lhs, this.myVar);
        this.normalRules.add(rule);
    }

    // When leaving a RelativeRule-Node,
    // we get the rhs and lhs from the faStack
    // and create a new rule,
    // which we add to the set of relative rules
    @Override
    public void outARelativeRule(ARelativeRule node)
    {
        TRSFunctionApplication rhs = this.faStack.pop();
        TRSFunctionApplication lhs = this.faStack.pop();
        Rule rule = Rule.create(lhs, rhs);
        this.relativeRules.add(rule);
    }

    // When leaving an EmptyrelRule-Node,
    // we get the lhs from the faStack,
    // use myVar as rhs,
    // and create a new rule,
    // which we add to the set of relative rules
    @Override
    public void outAEmptyrelRule(AEmptyrelRule node)
    {
        TRSFunctionApplication lhs = this.faStack.pop();
        Rule rule = Rule.create(lhs, this.myVar);
        this.relativeRules.add(rule);
    }

    // When leaving a LeftmostStrategydecl-Node,
    // we set the variable leftmost to true
    @Override
    public void outALeftmostStrategydecl(ALeftmostStrategydecl node)
    {
        this.leftmost = true;
    }

    // When leaving a RightmostStrategydecl-Node,
    // we set the variable rightmost to true
    @Override
    public void outARightmostStrategydecl(ARightmostStrategydecl node)
    {
        this.rightmost = true;
    }

    public boolean getRightmost() {
        return this.rightmost;
    }

    public boolean getLeftmost() {
        return this.leftmost;
    }


    public Set<Rule> getNormalRules() {
        return this.normalRules;
    }

    public Set<Rule> getRelativeRules() {
        return this.relativeRules;
    }

    public Set<String> getFunctionSymbolNames() {
        return this.fnames;
    }

    public TRSVariable getMyVar(){
        return this.myVar;
    }

}
