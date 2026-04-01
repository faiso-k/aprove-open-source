package aprove.verification.complexity.CpxTrsProblem.Processors;

import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxRelTrsProblem.Processors.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * docu-guess (fuhs):
 * The implemented transformation of non-constructor systems to constructor
 * systems appears to be adapted from the following paper:
 *
 * Satish Thatte
 * Implementing first-order rewriting with constructor systems
 * Theoretical Computer Science, 61(1):83-92, 1988.
 *
 * Idea: occurrences of defined symbols f below the root on the lhs of a rule
 * are replaced by a corresponding new constructor symbol c_f, and a
 * relative rule f(x_1, ..., x_n) -> c_f(x_1, ..., x_n) is added.
 */
public class CpxTrsNonCtorToCtorProcessor extends RuntimeComplexityRelTrsProcessor {

    public static class Arguments {
        public boolean justFullRewriting = false;
    }

    private Arguments args;

    @ParamsViaArgumentObject
    public CpxTrsNonCtorToCtorProcessor(Arguments args) {
        this.args = args;
    }

    @Override
    protected boolean isRuntimeComplexityRelTrsApplicable(RuntimeComplexityRelTrsProblem obl) {
        return Options.certifier == Certifier.NONE && !obl.isConstructorSystem() && (!args.justFullRewriting || obl.getRewriteStrategy() == RewriteStrategy.FULL);
    }

    @Override
    protected Result processRuntimeComplexityRelTrs(RuntimeComplexityRelTrsProblem trs, Abortion aborter) {
        FreshNameGenerator fng = new FreshNameGenerator(trs.getUsedNames(), FreshNameGenerator.APPEND_NUMBERS);
        Set<Rule> nonBasicRules = trs.getR().stream().filter(r -> !trs.isBasic(r.getLeft())).collect(toSet());
        Set<Rule> nonBasicRelRules = trs.getS().stream().filter(r -> !trs.isBasic(r.getLeft())).collect(toSet());
        Set<FunctionSymbol> nestedSymbols = union(nonBasicRules, nonBasicRelRules).stream().flatMap(r ->
          intersection(trs.getDefinedSymbols(), r.getLeft().getNonRootFunctionSymbols()).stream()
        ).collect(toSet());
        Set<Rule> newRelRules = new LinkedHashSet<>();
        Map<FunctionSymbol, FunctionSymbol> nestedDefSymbolToCtor = new LinkedHashMap<>();
        for (FunctionSymbol f: nestedSymbols) {
            nestedDefSymbolToCtor.put(f, FunctionSymbol.create(fng.getFreshName("c_" + f.getName(), true), f.getArity()));
        }
        for (FunctionSymbol f: nestedSymbols) {
            List<TRSVariable> vars = new ArrayList<>();
            for (int i = 0; i < f.getArity(); i++) {
                vars.add(TRSTerm.createVariable("x" + i));
            }
            FunctionSymbol fCtor = nestedDefSymbolToCtor.get(f);
            Rule rule = Rule.create(TRSTerm.createFunctionApplication(f, vars), TRSTerm.createFunctionApplication(fCtor, vars));
            newRelRules.add(rule);
        }
        Set<Rule> adaptedRules = adaptRules(nonBasicRules, trs, nestedDefSymbolToCtor);
        Set<Rule> adaptedRelRules = adaptRules(nonBasicRelRules, trs, nestedDefSymbolToCtor);
        Set<Rule> resultRules = new LinkedHashSet<>(trs.getR());
        resultRules.removeAll(nonBasicRules);
        resultRules.addAll(adaptedRules);
        Set<Rule> resultRelRules = new LinkedHashSet<>(trs.getS());
        resultRelRules.removeAll(nonBasicRelRules);
        resultRelRules.addAll(adaptedRelRules);
        resultRelRules.addAll(newRelRules);
        BasicObligation newObl = RuntimeComplexityRelTrsProblem.create(ImmutableCreator.create(resultRules),
            ImmutableCreator.create(resultRelRules), trs.getRewriteStrategy(), trs.STerminatesInnermost());
        return ResultFactory.proved(newObl, UpperBound.create(), new NonCtorToCtorProof());
    }

    private Set<Rule> adaptRules(Set<Rule> nonBasicRules, RuntimeComplexityRelTrsProblem trs, Map<FunctionSymbol, FunctionSymbol> nestedDefSymbolToCtor) {
        Set<Rule> adaptedRules = new LinkedHashSet<>();
        for (Rule r: nonBasicRules) {
            TRSFunctionApplication lhs = r.getLeft();
            for (Pair<Position, TRSFunctionApplication> p: lhs.getNonRootNonVariablePositionsWithSubTerms()) {
                Position pi = p.x;
                TRSFunctionApplication t = p.y;
                if (trs.isDefined(t.getRootSymbol())) {
                    FunctionSymbol fCtor = nestedDefSymbolToCtor.get(t.getRootSymbol());
                    TRSFunctionApplication newT = TRSTerm.createFunctionApplication(fCtor, t.getArguments());
                    lhs = (TRSFunctionApplication) lhs.replaceAt(pi, newT);
                }
            }
            adaptedRules.add(Rule.create(lhs, r.getRight()));
        }
        return adaptedRules;
    }

    private class NonCtorToCtorProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "transformed non-ctor to ctor-system";
        }

    }

}
