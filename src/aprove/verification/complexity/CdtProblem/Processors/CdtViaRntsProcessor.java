package aprove.verification.complexity.CdtProblem.Processors;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import aprove.prooftree.Export.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.Processors.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Search for upper bounds for CdtProblems via an abstraction to integer
 * problems (by reusing the existing processors for CpxRntsProblem).
 *
 * Issue: The two frameworks count rather different items to assemble
 * overall complexities ...
 *
 * @author Carsten Fuhs
 */
public class CdtViaRntsProcessor extends ProcessorSkeleton {

    /**
     * The strategy to convert a CpxWeightedTrsProblem to a CpxRntsProblem,
     * gathering some information about the runtime complexity of the root
     * symbols of the LHSs of some Cdts in the process. Should be
     * complexity-preserving.
     */
    private final String strategy;

    @ParamsViaArgumentObject
    public CdtViaRntsProcessor(Arguments arguments) {
        this.strategy = arguments.strategy;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (true || ! (obl instanceof CdtProblem)) {
            return false;
        }
        CdtProblem cdtProblem = (CdtProblem) obl;
        return cdtProblem.isConstructorSystem();
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
            Abortion aborter, RuntimeInformation rti) throws AbortionException {
        CdtProblem cdtProblem = (CdtProblem) obl;
        if (cdtProblem.getS().isEmpty()) {
            // silly hack to use functionality from CdtProblemProcessor
            // to deal with problems with empty S without exposing
            // CdtProblemProcessor internals
            CdtProblemProcessor emptyProc = new CdtUnreachableProcessor();
            return emptyProc.process(cdtProblem, oblNode, aborter, rti);
        }

        // (1) convert to weighted TRS problem where S has weight 1 and
        //     (R \cup D \setminus S) has weight 0
        
        CpxWeightedTrsProblem weightedTrs = toWeightedTrs(cdtProblem);
        aborter.checkAbortion();
        
        CpxWeightedTrsRenamingProcessor renamingProc = new CpxWeightedTrsRenamingProcessor();
        Pair<CpxWeightedTrsProblem, Map<FunctionSymbol, FunctionSymbol>> renamingResult;
        renamingResult = renamingProc.rename(weightedTrs, aborter);
        CpxWeightedTrsProblem renamedWeightedTrs = renamingResult.x;
        Map<FunctionSymbol, FunctionSymbol> symbolRenaming = renamingResult.y;

        // (2) invoke subMachine with strategy that should give us complexities
        //     for some of the root symbols of S as an oracle
        //     (this part is inspired by SemanticLabellingProcessor)

        BasicObligationNode weightedTrsNode = new BasicObligationNode(renamedWeightedTrs);
        // TODO maybe create UserStrategy in constructor (requires thread-safe strategy)
        UserStrategy userStrategy = new VariableStrategy(this.strategy);
        StrategyExecutionHandle handle =
            Machine.theMachine.startSubMachine(
                userStrategy,
                rti.getProgram(),
                weightedTrsNode,
                null,
                aborter.getClocks(),
                false);

        HandleChecker.check(handle, aborter);

        // okay, we have the result after the strategy
        ExecutableStrategy result = handle.getResult();
        if (result == null || result.isFail()) {
            // no progress with the strategy
            return ResultFactory.unsuccessful(this.getClass().getSimpleName() +
                "'s strategy " + this.strategy + " unsuccessful.");
        }

        Success success = (Success) result;
        List<BasicObligationNode> newProblems = success.getPositions();
        int numberOfSubproblems = newProblems.size();
        if (numberOfSubproblems != 1) {
            // TODO more graciously: just return unsuccessful();
            // the current behavior may however be more helpful
            // to strategy authors
            throw new RuntimeException("Unexpected number " +
                    numberOfSubproblems + " of BOblNodes from strategy " +
                    this.strategy + " (expected: 1)!");
        }

        // now there can be only one
        BasicObligationNode theBoblNode = newProblems.get(0);
        BasicObligation theBobl = theBoblNode.getBasicObligation();
        if (! (theBobl instanceof CpxRntsProblem)) {
            throw new RuntimeException("Unsuitable strategy " + this.strategy +
                " returning a " + theBobl.getClass().getSimpleName() +
                " instead of a " + CpxRntsProblem.class.getSimpleName() +
                "!");
        }
        CpxRntsProblem cpxRnts = (CpxRntsProblem) theBobl;
        aborter.checkAbortion();

        // the complexity result encapsulated by cpxRnts presumably also
        // carries over to cdtProblem; take the max for the root symbols of S
        // left-hand sides

        // TODO somehow check that the strategy did not sneakily do things
        //      that are not "complexity-preserving" -- that is, all its
        //      processors were "sound"

        // map S root symbols to the corresponding Cdts
        Map<FunctionSymbol, Set<Cdt>> fToSCdts = new LinkedHashMap<>();
        for (Cdt cdt : cdtProblem.getS()) {
            FunctionSymbol f = cdt.getRootSymbol();
            Set<Cdt> cdts = fToSCdts.get(f);
            if (cdts == null) {
                cdts = new LinkedHashSet<>();
                fToSCdts.put(f, cdts);
            }
            cdts.add(cdt);
        }

        // now to the actual progress
        ComplexityValue cpxValue = ComplexityValue.constant();
        Set<Cdt> strictTuples = new LinkedHashSet<>();
        for (Map.Entry<FunctionSymbol, Set<Cdt>> fToCdts : fToSCdts.entrySet()) {
            FunctionSymbol fun = fToCdts.getKey();
            // remember that fun may have got renamed in cpxRnts
            FunctionSymbol renamedFun = symbolRenaming.get(fun);
            if (renamedFun == null) {
                // not renamed after all, so the original name needs to be used
                renamedFun = fun;
            }
            if (cpxRnts.hasResult(renamedFun)) {
                ComplexitySummary cpx = cpxRnts.getResult(renamedFun);
                if (cpx.hasRuntime()) {
                    // hooray!
                    ComplexityValue cpxVal = cpx.getRuntime();
                    cpxValue = cpxValue.max(cpxVal);
                    Set<Cdt> cdts = fToCdts.getValue();
                    strictTuples.addAll(cdts);
                }
            }
        }

        // (3) create sub-problem without those S-cdts for which we know
        //     bounds (if any); here a bound for a Cdt's root symbol carries
        //     over to the Cdt itself
        if (strictTuples.isEmpty()) {
            return ResultFactory.unsuccessful("CpxRnts was created successfully for CdtProblem; but alas, no useful complexity info was found.");
        }
        LinkedHashSet<Cdt> newS = new LinkedHashSet<Cdt>(cdtProblem.getS());
        newS.removeAll(strictTuples);
        LinkedHashSet<Cdt> newK = new LinkedHashSet<Cdt>(cdtProblem.getK());
        newK.addAll(strictTuples);
        CdtProblem newCdtProblem = cdtProblem.createSubproblem(
                cdtProblem.getGraph(),
                ImmutableCreator.create(newS),
                ImmutableCreator.create(newK));

        UpperBound upperBound = UpperBound.create(new SumComputation(cpxValue));
        Exportable subProof = new Exportable() {

            @Override
            public String toString() {
                return this.export(new PLAIN_Util());
            }

            @Override
            public String export(Export_Util o) {
                String internalProof = new ParallelPlainExportManager(weightedTrsNode, "internal").export();
                StringBuilder res = new StringBuilder();
                for (String line : internalProof.split("\n")) {
                    res.append("| ");
                    res.append(line);
                    res.append('\n');
                }
                return o.preFormatted(res.toString());
            }
        };
        Proof proof = new CdtViaRntsProof(strictTuples, subProof);
        return ResultFactory.proved(newCdtProblem, upperBound, proof);
    }

    /**
     * Converts (D, S, K, R) to S with weight 1 and (D \setminus S) \cup R with
     * weight 0.
     *
     * @param cdtProblem (D, S, K, R); non-null
     * @return S with weight 1 and (D \setminus S) \cup R with weight 0
     */
    private static CpxWeightedTrsProblem toWeightedTrs(CdtProblem cdtProblem) {
        Set<WeightedRule> weightedRules = new LinkedHashSet<>();
        ImmutableSet<Cdt> oldS = cdtProblem.getS();
        ImmutableSet<Cdt> oldTuples = cdtProblem.getTuples();
        Set<Rule> oldR = cdtProblem.getR();

        // generate the weight 1 part ...
        for (Cdt cdt : oldS) {
            weightedRules.add(WeightedRule.create(cdt.getRule(),1));
        }

        // ... then the weight 0 part
        for (Cdt cdt : oldTuples) {
            if (! oldS.contains(cdt)) {
                weightedRules.add(WeightedRule.create(cdt.getRule(),0));
            }
        }
        for (Rule rule : oldR) {
            weightedRules.add(WeightedRule.create(rule,0));
        }

        CpxWeightedTrsProblem res = CpxWeightedTrsProblem.create(ImmutableCreator.create(weightedRules), cdtProblem.isInnermost());
        return res;
    }

    public static class CdtViaRntsProof extends CpxProof {
        private Set<Cdt> strictTuples;
        private Exportable subProof;

        public CdtViaRntsProof(Set<Cdt> strictTuples, Exportable subProof) {
            this.strictTuples = strictTuples;
            this.subProof = subProof;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o.escape("Via a temporary abstraction to the naturals, complexity bounds for the following Cdts were found: "));
            sb.append(o.set(this.strictTuples, Export_Util.RULES));
            sb.append(o.cond_linebreak());
            sb.append(o.escape("The proof underlying this step is as follows: "));
            sb.append(o.linebreak());
            sb.append(o.export(this.subProof));
            return sb.toString();
        }
    }

    public static class Arguments {
        /** Sub-strategy to transform CpxWeightedTrsProblem to
         *  (partially) solved CpxRntsProblem with information
         *  on runtime bounds for some of the function symbols
         */ 
        public String strategy = "cdtRIntHelper";
    }
}
