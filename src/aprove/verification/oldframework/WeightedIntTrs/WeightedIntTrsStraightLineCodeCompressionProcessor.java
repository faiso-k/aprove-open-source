package aprove.verification.oldframework.WeightedIntTrs;

import static aprove.verification.dpframework.IDPProblem.utility.IDPPredefinedMap.*;
import static aprove.verification.dpframework.ResultFactory.*;
import static aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.TerminationSCCToIDPv1Processor.*;
import static aprove.verification.oldframework.IntTRS.PoloRedPair.ToolBox.*;
import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.Collections.*;
import java.util.*;
import java.util.Map.*;
import java.util.stream.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.JBCOptions.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class WeightedIntTrsStraightLineCodeCompressionProcessor extends ProcessorSkeleton {

    public static class Arguments {

        public static StaticOption<Boolean> cliPropagateLowerBounds = new StaticOption<>();
        private InstanceOption<Boolean> propagateLowerBounds = new InstanceOption<>(false, cliPropagateLowerBounds);

        public boolean propagateLowerBounds() {
            return propagateLowerBounds.get();
        }

        public void setPropagateLowerBounds(boolean b) {
            propagateLowerBounds.set(b);
        }

    }

    private Arguments args;

    @ParamsViaArgumentObject
    public WeightedIntTrsStraightLineCodeCompressionProcessor(Arguments args) {
        this.args = args;
    }

    private static class FunctionSymbolMap <T extends AbstractWeightedIntRule<T>> {

        CollectionMap<FunctionSymbol, T> incomming = new CollectionMap<>();
        CollectionMap<FunctionSymbol, T> outgoing = new CollectionMap<>();

        FunctionSymbolMap(Set<T> rules) {
            for (T r : rules) {
                for (TRSFunctionApplication fA : r.getRight()) {
                    incomming.add(fA.getRootSymbol(), r);
                }
                outgoing.add(r.getRootSymbol(), r);
            }
        }

        Collection<T> getIncomming(FunctionSymbol f) {
            return incomming.getNotNull(f);
        }

        Collection<T> getOutgoing(FunctionSymbol f) {
            return outgoing.getNotNull(f);
        }

        void replaceOutgoing(FunctionSymbol f, T oldRule, T newRule) {
            replace(outgoing, f, oldRule, newRule);
        }

        void replaceIncomming(FunctionSymbol f, T oldRule, T newRule) {
            replace(incomming, f, oldRule, newRule);
        }

        void replace(CollectionMap<FunctionSymbol, T> m, FunctionSymbol f, T oldRule, T newRule) {
            m.removeFromCollection(f, oldRule);
            m.add(f, newRule);
        }

    }

    private static class RuleCompressor <T extends AbstractWeightedIntRule<T>> {

        private FunctionSymbolMap<T> fsm;
        private Set<FunctionSymbol> seen = new LinkedHashSet<>();
        private Set<T> res = new LinkedHashSet<>();
        private Map<T, Set<T>> log = new LinkedHashMap<>();
        private Set<T> toRemove = new LinkedHashSet<>();
        private Stack<FunctionSymbol> todo = new Stack<>();
        private FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
        private FunctionSymbol start;

        RuleCompressor(AbstractWeightedIntTermSystem<T> trs) {
            fsm = new FunctionSymbolMap<>(trs.getRules());
            this.start = trs.getStartTerm().getRootSymbol();
            todo.push(start);
        }

        void compressRules() {
            do {
                FunctionSymbol current = todo.pop();
                if (seen.add(current)) {
                    Collection<T> out = fsm.getOutgoing(current);
                    res.addAll(out);
                    tryToRemove(current);
                    for (T rule : out) {
                        for (TRSFunctionApplication fA : rule.getRight()) {
                            todo.push(fA.getRootSymbol());
                        }
                    }
                }
            } while (!todo.isEmpty());
            res.removeAll(toRemove);
        }

        void tryToRemove(FunctionSymbol f) {
            if (!f.equals(start)) {
                Collection<T> in = fsm.getIncomming(f);
                Collection<T> out = fsm.getOutgoing(f);
                Stream<FunctionSymbol> preds = in.stream().map(x -> x.getRootSymbol());
                boolean hasSelfLoops = preds.anyMatch(x -> x.equals(f));
                if (!hasSelfLoops) {
                    long numPreds = in.size();
                    long numSuccs = out.size();
                    if (numPreds == 1 && numSuccs == 1) {
                        for (T inRule: in){
                            if (inRule.getRight().size() != 1) {
                                continue;
                            }
                            for (T outRule: out){
                                T chainedRule = tryToChain(inRule, outRule);
                                if (chainedRule != null) {
                                    toRemove.add(inRule);
                                    toRemove.add(outRule);
                                    Set<T> originalRules = new LinkedHashSet<>();
                                    if (log.containsKey(inRule)) {
                                        originalRules.addAll(log.get(inRule));
                                        log.remove(inRule);
                                    } else {
                                        originalRules.add(inRule);
                                    }
                                    if (log.containsKey(outRule)) {
                                        originalRules.addAll(log.get(outRule));
                                        log.remove(outRule);
                                    } else {
                                        originalRules.add(outRule);
                                    }
                                    log.put(chainedRule, originalRules);
                                    updateFunctionSymbolMap(inRule, outRule, chainedRule);
                                }
                            }
                        }
                    }
                }
            }
        }

        T tryToChain(T inRuleArg, T outRuleArg) {
            Set<TRSVariable> allVariables = union(inRuleArg.getVariables(), outRuleArg.getVariables());
            T outRule = renameVariables(outRuleArg, allVariables);
            T inRule = moveArithmeticFromRhsToConstraint(inRuleArg);
            TRSFunctionApplication inRuleRhs = inRule.getRight().iterator().next();
            TRSSubstitution sigma = inRuleRhs.getMGU(outRule.getLeft());
            if (sigma == null) {
                debug("straight line code compression: could not unify " + inRule + " and " + outRule);
                return null;
            } else {
                TRSFunctionApplication newLhs = inRule.getLeft().applySubstitution(sigma);
                List<TRSTerm> newOutputVariables = applySubstitution(inRule.getLeftOutputVariables(), sigma);
                List<TRSFunctionApplication> newRhs = new ArrayList<>(outRule.getRight());
                newRhs.replaceAll(fA -> fA.applySubstitution(sigma));
                TRSFunctionApplication newCond = buildAnd(inRule.getCondition().applySubstitution(sigma),
                        outRule.getCondition().applySubstitution(sigma));
                Map<String, String> stringMap = new LinkedHashMap<>();
                for (Entry<TRSVariable, ? extends TRSTerm> e: sigma.toMap().entrySet()) {
                    stringMap.put(e.getKey().toString(), e.getValue().toString());
                }
                SimplePolynomial upperBound = inRule.getUpperBound().replace(stringMap).plus(outRule.getUpperBound().replace(stringMap));
                SimplePolynomial lowerBound = inRule.getLowerBound()
                        .map(lB -> lB.replace(stringMap).plus(outRule.getLowerBound().get().replace(stringMap)))
                        .orElse(null);
                if (newRhs.size() == 1 && upperBound.isConstant()
                        && (lowerBound == null || lowerBound.isConstant())) {
                    IGeneralizedRule iR = IGeneralizedRule.create(newLhs, newRhs.iterator().next(), newCond, newOutputVariables);
                    iR = removeTrivialConstraints(singleton(iR), DEFAULT_MAP).iterator().next();
                    newLhs = iR.getLeft();
                    newRhs = Collections.singletonList((TRSFunctionApplication)iR.getRight());
                    newCond = (TRSFunctionApplication)iR.getCondTerm();
                    newOutputVariables = iR.getLeftOutputVariables();
                }
                return inRuleArg.copy(newLhs, newRhs, newCond, upperBound, lowerBound, newOutputVariables);
            }
        }

        private List<TRSTerm> applySubstitution(List<TRSTerm> args, TRSSubstitution sigma) {
            List<TRSTerm> newArgs = null;
            if (args != null) {
                newArgs = new ArrayList<>();
                for (TRSTerm arg: args) {
                    newArgs.add(arg.applySubstitution(sigma));
                }
            }
            return newArgs;
        }

        private T moveArithmeticFromRhsToConstraint(T rule) {
            List<TRSFunctionApplication> newRhs = new ArrayList<>(rule.getRight().size());
            TRSFunctionApplication cond = rule.getCondition();
            for (TRSFunctionApplication fA : rule.getRight()) {
                Pair<TRSFunctionApplication, TRSFunctionApplication> pair = moveArithmeticFromRhsToConstraint(fA, cond);
                newRhs.add(pair.x);
                cond = pair.y;
            }
            return rule.copy(rule.getLeft(), newRhs, cond, rule.getLeftOutputVariables());
        }

        private Pair<TRSFunctionApplication, TRSFunctionApplication> moveArithmeticFromRhsToConstraint(TRSFunctionApplication fA, TRSFunctionApplication cond) {
            if (!ToolBox.PREDEFINED.isPredefined(fA.getFunctionSymbol()))
                return new Pair<>(fA, cond);
            boolean changed = false;
            List<TRSTerm> args = new ArrayList<>();
            for (TRSTerm arg: fA.getArguments()) {
                if (arg.isVariable()) {
                    args.add(arg);
                } else {
                    TRSVariable x = TRSTerm.createVariable(fng.getFreshName("x", false));
                    args.add(x);
                    cond = buildAnd(cond, buildEq(x, arg));
                    changed = true;
                }
            }
            if (changed)
                return new Pair<>(TRSTerm.createFunctionApplication(fA.getRootSymbol(), args), cond);
            else
                return new Pair<>(fA, cond);

        }

        T renameVariables(T r, Set<TRSVariable> allVariables) {
            Map<TRSVariable, TRSVariable> renamingMap = new LinkedHashMap<>();
            for (TRSVariable x : allVariables) {
                renamingMap.put(x, TRSTerm.createVariable(fng.getFreshName(x.getName(), false)));
            }
            return r.getWithRenamedVariables(renamingMap);
        }

        void updateFunctionSymbolMap(T inRule, T outRule, T chainedRule) {
            res.add(chainedRule);
            fsm.replaceOutgoing(inRule.getRootSymbol(), inRule, chainedRule);
            for (TRSFunctionApplication fA : outRule.getRight()) {
                FunctionSymbol outLocation = fA.getRootSymbol();
                fsm.replaceIncomming(outLocation, outRule, chainedRule);

            }
        }

    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        return processInternal((AbstractWeightedIntTermSystem<?>) obl);
    }

    private <T extends AbstractWeightedIntRule<T>> Result processInternal(AbstractWeightedIntTermSystem<T> obl) {
        RuleCompressor<T> compressor = compressRules(obl);
        if (compressor.res.equals(obl.getRules())) {
            return unsuccessful();
        } else {
            // TODO: this processor is *not* equivalent since it uses "removeTrivialConstraints", which does strange things...
            if (WeightedIntTrsStraightLineCodeCompressionProcessor.this.args.propagateLowerBounds()) {
                return proved(obl.copyWithNewRules(compressor.res),
                        SoundUpperUnsoundLowerBound.forConcreteBounds(),
                    new StraightLineCodeCompressionProof<>(obl.getRules().size(), compressor.res.size(), compressor.log));
            } else {
                return proved(obl.copyWithNewRules(compressor.res),
                        UpperBound.forConcreteBounds(),
                    new StraightLineCodeCompressionProof<>(obl.getRules().size(), compressor.res.size(), compressor.log));
            }
        }
    }

    private static <T extends AbstractWeightedIntRule<T>> RuleCompressor<T> compressRules(AbstractWeightedIntTermSystem<T> irs) {
        RuleCompressor<T> res = new RuleCompressor<>(irs);
        res.compressRules();
        return res;
    }

    private static void debug(String s) {
        if (Globals.DEBUG_FFROHN) {
            System.err.println(s);
        }
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof AbstractWeightedIntTermSystem<?>;
    }

    public static class StraightLineCodeCompressionProof <T extends AbstractWeightedIntRule<T>> extends DefaultProof {

        int beforeCompression, afterCompression;
        Map<T, Set<T>> log;

        public StraightLineCodeCompressionProof(int beforeCompression, int afterCompression,
                Map<T, Set<T>> log) {
            this.beforeCompression = beforeCompression;
            this.afterCompression = afterCompression;
            this.log = log;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("Compressed ").append(beforeCompression).append(" to ")
                    .append(afterCompression).append(" rules").append(o.newline());
            for (Entry<T, Set<T>> e: log.entrySet()) {
                sb.append("obtained");
                sb.append(o.linebreak());
                sb.append(e.getKey().export(o));
                sb.append(o.linebreak());
                sb.append("by chaining");
                sb.append(o.newline());
                Iterator<T> it = e.getValue().iterator();
                while (it.hasNext()) {
                    sb.append(it.next().export(o));
                    if (it.hasNext()) {
                        sb.append(o.linebreak());
                    }
                }
                sb.append(o.paragraph());
            }
            return sb.toString();
        }
    }

}
