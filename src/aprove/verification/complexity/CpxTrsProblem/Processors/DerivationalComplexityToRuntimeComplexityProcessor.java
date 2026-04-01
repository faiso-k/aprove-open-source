package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;

import aprove.Globals;
import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Processor to convert DerivationalComplexityProblem R/S to an
 * instrumented RuntimeComplexityProblem R'/S' where
 * either R' = R and S' \supseteq S and rc(R'/S') = dc(R/S), 
 * or R' \supset R and S' = S and rc(R'/S') = max(O(n), dc(R/S)).
 *
 * @author Carsten Fuhs
 */
public class DerivationalComplexityToRuntimeComplexityProcessor extends ProcessorSkeleton {

    /** The default name for the function symbol of the function that
     *  does the actual conversion of the arguments via rewrite rules.
     */  
    private static final String CONVERT_SYMBOL_NAME = "encArg";

    /** The default suffix for the function symbol of the function that
     *  does the actual conversion of the root via rewrite rules.
     */  
    private static final String ENCODE_SYMBOL_PREFIX = "encode";

    /** The default suffix for the constructor symbols representing the
     *  defined symbols.
     */  
    private static final String CONS_SYMBOL_PREFIX = "cons";

    /** Prefix for the name of fresh variables. */
    private static final String VAR_PREFIX = "x_";

    /** Shall we introduce the extra rules in S rather than in R? */
    private final boolean introRelativeRules;

    @ParamsViaArgumentObject
    public DerivationalComplexityToRuntimeComplexityProcessor(Arguments arguments) {
        this.introRelativeRules = arguments.introRelativeRules;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        DerivationalComplexityRelTrsProblem derivCpxProblem = (DerivationalComplexityRelTrsProblem) obl; 
        ImmutableSet<Rule> R = derivCpxProblem.getR();
        if (R.isEmpty()) { // TODO factor out
            return ResultFactory.provedWithValue(ComplexityYNM.CONSTANT, new RIsEmptyProof());
        }
        ImmutableSet<Rule> S = derivCpxProblem.getS();
        Set<Rule> allRules = new LinkedHashSet<>();
        allRules.addAll(R);
        allRules.addAll(S);
        Set<Rule> encodingRules = generateEncodingRulesForRules(allRules);
        ImmutableSet<Rule> newR, newS;
        if (this.introRelativeRules) {
            newR = R;
            Set<Rule> protoNewS = new LinkedHashSet<>();
            protoNewS.addAll(encodingRules);
            protoNewS.addAll(S);
            newS = ImmutableCreator.create(protoNewS);
        } else {
            Set<Rule> protoNewR = new LinkedHashSet<>();
            protoNewR.addAll(encodingRules);
            protoNewR.addAll(R);
            newR = ImmutableCreator.create(protoNewR);
            newS = S;
        }
        BasicObligation newBobl;
        if (newS.isEmpty()) {
            newBobl = RuntimeComplexityTrsProblem.create(newR, derivCpxProblem.getRewriteStrategy());
        } else {
            newBobl = RuntimeComplexityRelTrsProblem.create(newR, newS, derivCpxProblem.getRewriteStrategy(), false);
        }
        Proof proof = new DerivationalComplexityToRuntimeComplexityProof(encodingRules, this.introRelativeRules); 
        if (this.introRelativeRules) {
            return ResultFactory.proved(newBobl, BothBounds.create(), proof);
        } else {
            // we're SOUND but not necessarily COMPLETE because the additional
            // rules may artificially bump up the complexity to linear
            return ResultFactory.proved(newBobl, SoundUpperUnsoundLowerBound.create(), proof);
        }
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return (obl instanceof DerivationalComplexityTrsProblem || obl instanceof DerivationalComplexityRelTrsProblem)
                && Options.certifier == Certifier.NONE;
    }

    /**
     * @param rules the rules for which we want to generate the encoding rules
     * @return the encoding rules
     */
    private static LinkedHashSet<Rule> generateEncodingRulesForRules(Set<Rule> rules) {
        Set<FunctionSymbol> allSyms = CollectionUtils.getFunctionSymbols(rules);
        Set<FunctionSymbol> definedSyms = CollectionUtils.getRootSymbols(rules);
        Set<FunctionSymbol> constructorSyms = new LinkedHashSet<>();
        for (FunctionSymbol f : allSyms) {
            if (! definedSyms.contains(f)) {
                constructorSyms.add(f);
            }
        }
        int maxArity = CollectionUtils.getMaxArity(allSyms);
        return generateEncodingRulesForSyms(allSyms, definedSyms, constructorSyms, maxArity);
    }

    /**
     * Generate rules expressing the conversion from basic terms over an
     * extended signature to arbitrary terms over the original signature.
     *
     * @param allSyms the union of definedSyms and constructorSyms; non-null
     * @param definedSyms to be treated like defined symbols by the conversion;
     *  non-null
     * @param constructorSyms to be treated like constructor symbols by the
     *  conversion; non-null
     * @param maxArity the maximum arity of the FunctionSymbols in allSyms
     * @return rules encoding the conversion from basic terms over an extended
     *  signature to arbitrary terms over the original signature
     */
    private static LinkedHashSet<Rule> generateEncodingRulesForSyms(Set<FunctionSymbol> allSyms,
            Set<FunctionSymbol> definedSyms, Set<FunctionSymbol> constructorSyms, int maxArity) {
        LinkedHashSet<Rule> result = new LinkedHashSet<>();

        // fresh name generation infrastructure
        Set<String> used = CollectionUtils.getNames(definedSyms);
        used.addAll(CollectionUtils.getNames(constructorSyms));
        FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.APPEND_NUMBERS);
        // make unary converter symbol (let's call it 'conv')
        String freshConvName = fridge.getFreshName(CONVERT_SYMBOL_NAME, false);
        fridge.lockName(freshConvName);
        FunctionSymbol fConv = FunctionSymbol.create(freshConvName, 1); 

        // make fresh vars for rules
        List<TRSVariable> vars = makeVars(fridge, maxArity);

        // for constructor symbols f: make conv(f(x_1, ..., x_n)) -> f(conv(x_1), ..., conv(x_n))
        for (FunctionSymbol f : constructorSyms) {
            Rule rule = encodeConvRule(fConv, f, f, vars);
            result.add(rule);
        }

        // for defined symbols f: make conv(cons_f(x_1, ..., x_n)) -> f(conv(x_1), ..., conv(x_n))
        for (FunctionSymbol f : definedSyms) {
            String freshName = fridge.getFreshName(CONS_SYMBOL_PREFIX + "_" + f.getName(), false);
            fridge.lockName(freshName);
            FunctionSymbol fCons = FunctionSymbol.create(freshName, f.getArity());
            Rule argConvRule = encodeConvRule(fConv, fCons, f, vars);
            result.add(argConvRule);
        }

        // for all symbols f: make enc_f(x_1, ..., x_n) -> f(conv(x_1), ..., conv(x_n))
        for (FunctionSymbol f : allSyms) {
            String freshEncName = fridge.getFreshName(ENCODE_SYMBOL_PREFIX + "_" + f.getName(), false);
            fridge.lockName(freshEncName);
            FunctionSymbol fEnc = FunctionSymbol.create(freshEncName, f.getArity());
            Rule encRule = encodeEncRule(fEnc, f, fConv, vars);
            result.add(encRule);
        }

        return result;
    }

    /**
     * Returns fConv(leftSym(x_1, ..., x_n)) -> rightSym(fConv(x_1), ..., fConv(x_n)).
     * @param fConv non-null
     * @param leftSym non-null
     * @param rightSym non-null
     * @param vars [x_1, ..., x_maxArity]
     * @return fConv(leftSym(x_1, ..., x_n)) -> rightSym(fConv(x_1), ..., fConv(x_n))
     */
    private static Rule encodeConvRule(FunctionSymbol fConv,
            FunctionSymbol leftSym, FunctionSymbol rightSym, List<TRSVariable> vars) {
        int arity = leftSym.getArity();
        if (Globals.useAssertions) {
            assert arity == rightSym.getArity();
        }

        // goal: build rule   lhs -> rhs
        // lhs = fConv(leftSym(x_1, ..., x_n))
        ArrayList<TRSVariable> argVars = new ArrayList<>(vars.subList(0, arity));
        ImmutableList<TRSVariable> argVarsImm = ImmutableCreator.create(argVars);
        TRSTerm leftSymApp = TRSTerm.createFunctionApplication(leftSym, argVarsImm);
        TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(fConv, leftSymApp);

        // rhs = rightSym(fConv(x_1), ..., fConv(x_n))
        ArrayList<TRSFunctionApplication> rhsArgs = new ArrayList<>(arity);
        for (int i = 0; i < arity; ++i) {
            TRSVariable v = vars.get(i);
            TRSFunctionApplication fConvV = TRSTerm.createFunctionApplication(fConv, v);
            rhsArgs.add(fConvV);
        }
        ImmutableList<TRSFunctionApplication> rhsArgsImm = ImmutableCreator.create(rhsArgs);
        TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(rightSym, rhsArgsImm); 
        return Rule.create(lhs, rhs);
    }

    /**
     * Returns fEnc(x_1, ..., x_n) -> rightSym(argConv(x_1), ..., argConv(x_n)).
     * @param fEnc non-null
     * @param rightSym non-null
     * @param argConv non-null
     * @param vars [x_1, ..., x_maxArity]
     * @return fEnc(x_1, ..., x_n) -> rightSym(argConv(x_1), ..., argConv(x_n))
     */
    private static Rule encodeEncRule(FunctionSymbol fEnc,
            FunctionSymbol rightSym, FunctionSymbol argConv, List<TRSVariable> vars) {
        int arity = fEnc.getArity();
        if (Globals.useAssertions) {
            assert arity == rightSym.getArity();
        }

        // goal: build rule   lhs -> rhs
        // lhs = fEnc(x_1, ..., x_n))
        ArrayList<TRSVariable> argVars = new ArrayList<>(vars.subList(0, arity));
        ImmutableList<TRSVariable> argVarsImm = ImmutableCreator.create(argVars);
        TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(fEnc, argVarsImm);

        // rhs = rightSym(fConv(x_1), ..., fConv(x_n))
        ArrayList<TRSFunctionApplication> rhsArgs = new ArrayList<>(arity);
        for (int i = 0; i < arity; ++i) {
            TRSVariable v = vars.get(i);
            TRSFunctionApplication fConvV = TRSTerm.createFunctionApplication(argConv, v);
            rhsArgs.add(fConvV);
        }
        ImmutableList<TRSFunctionApplication> rhsArgsImm = ImmutableCreator.create(rhsArgs);
        TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(rightSym, rhsArgsImm); 
        return Rule.create(lhs, rhs);
    }

    /**
     * Returns a list of distinct fresh variables, with length howMany.
     * Side effect: fridge will no longer consider the names of the new
     * variables as fresh.
     *
     * @param fridge generates names for variables, non-null
     * @param howMany number of fresh variables to generate
     * @return a list of distinct fresh variables, with length howMany
     */
    private static ArrayList<TRSVariable> makeVars(FreshNameGenerator fridge, int howMany) {
        ArrayList<TRSVariable> res = new ArrayList<>(howMany);
        for (int i = 0; i < howMany; ++i) {
            String proposedName = VAR_PREFIX + (i+1);
            String freshName = fridge.getFreshName(proposedName, false);
            fridge.lockName(freshName);
            TRSVariable var = TRSTerm.createVariable(freshName);
            res.add(var);
        }
        return res;
    }

    private class DerivationalComplexityToRuntimeComplexityProof extends DefaultProof  {

        private Set<Rule> newRules;
        private boolean introRelativeRules;

        private DerivationalComplexityToRuntimeComplexityProof(Set<Rule> newRules, boolean introRelativeRules) {
            this.newRules = newRules;
            this.introRelativeRules = introRelativeRules;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("The following rules have been added to " +
                    (this.introRelativeRules ? 'S' : 'R') +
                    " to convert the given derivational complexity problem to a runtime complexity problem:");
            result.append(o.cond_linebreak());
            result.append(o.set(this.newRules, Export_Util.RULES));
            result.append(o.cond_linebreak());
            return result.toString();
        }
    }

    private class RIsEmptyProof extends DefaultProof  {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "R is empty";
        }
    }

    public static class Arguments {
        public boolean introRelativeRules = true;
    }
}
