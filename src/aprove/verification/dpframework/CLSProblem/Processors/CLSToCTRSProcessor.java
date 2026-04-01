package aprove.verification.dpframework.CLSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CLSProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

@NoParams
public class CLSToCTRSProcessor extends CLSProcessor {

    @Override
    public boolean isCLSApplicable(CLSProblem obl) {
        return true;
    }

    @Override
    protected Result processCLS(CLSProblem problem, Abortion aborter) throws AbortionException {
        CTRSProblem ctrs = CLSToCTRSProcessor.CLSToCTRS(problem);
        return ResultFactory.proved(ctrs, YNMImplication.SOUND, new CLSToCTRSProof());
    }

    public static CTRSProblem CLSToCTRS(CLSProblem problem) {
        Set<Rule> newRules = new LinkedHashSet<Rule>();
        Set<ConditionalRule> newCondRules = new LinkedHashSet<ConditionalRule>();
        CLSToCTRSProcessor.extractRules(problem.getRules(), newRules, newCondRules, newRules);
        CTRSProblem ctrs = CTRSProblem.create(ImmutableCreator.create(newRules), ImmutableCreator.create(newCondRules));
        return ctrs;
    }

    static void extractRules(Collection<ConditionalRule> rules, Set<Rule> newRules, Set<ConditionalRule> newCondRules, Set<Rule> builtInRules) {
        Map<FunctionSymbol,FunctionSymbol> predefs = new LinkedHashMap<FunctionSymbol,FunctionSymbol>();
        for (ConditionalRule rule : rules) {
            TRSFunctionApplication newLeft = (TRSFunctionApplication) CLSToCTRSProcessor.extractTerm(rule.getLeft(),predefs, builtInRules);
            TRSFunctionApplication newRight = (TRSFunctionApplication) CLSToCTRSProcessor.extractTerm(rule.getRight(),predefs, builtInRules);
            ImmutableList<Condition> conds = rule.getConditions();
            List<Condition> newConds = new ArrayList<Condition>(conds.size());
            for (Condition cond : conds) {
                Condition newCond = Condition.create(CLSToCTRSProcessor.extractTerm(cond.getLeft(), predefs, builtInRules), CLSToCTRSProcessor.extractTerm(cond.getRight(), predefs, builtInRules), cond.getType());
                newConds.add(newCond);
            }
            Rule newRule = Rule.create(newLeft, newRight);
            if (newConds.isEmpty()) {
                newRules.add(newRule);
            } else {
                newCondRules.add(ConditionalRule.create(newRule, ImmutableCreator.create(newConds)));
            }
        }
    }

    // FIXME: make private
    static TRSTerm extractTerm(TRSTerm term, Map<FunctionSymbol, FunctionSymbol> predefs, Set<Rule> newRules) {
        if (term.isVariable()) {
            return term;
        }
        TRSFunctionApplication fApp = (TRSFunctionApplication) term;
        FunctionSymbol f = fApp.getRootSymbol();
        if (f.getArity() == 0) {
            try {
                int constant = Integer.parseInt(f.getName());
                return PredefinedFunctionsManagerNegPos.numberToTerm(constant);
            } catch (NumberFormatException e) {}
        }
        if (PredefinedFunctionsManagerNegPos.hasRules(f)) {
            FunctionSymbol newF = predefs.get(f);
            if (newF == null) {
                Pair<Set<Rule>,FunctionSymbol> pair = PredefinedFunctionsManagerNegPos.generateRules(f);
                newRules.addAll(pair.x);
                newF = pair.y;
                predefs.put(f,newF);
            }
            f = newF;
        }
        ImmutableList<? extends TRSTerm> args = fApp.getArguments();
        List<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
        for (TRSTerm arg : args) {
            newArgs.add(CLSToCTRSProcessor.extractTerm(arg, predefs, newRules));
        }
        TRSFunctionApplication newFApp =
            TRSTerm.createFunctionApplication(
                f,
                (ImmutableArrayList<? extends TRSTerm>)ImmutableCreator.create(newArgs)
            );
        return newFApp;
    }

    public class CLSToCTRSProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Sliced variables";
        }

    }

}
