package aprove.verification.complexity.CpxWeightedTrsProblem.Processors;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Renames predefined symbols (e.g. if - is used as function symbol)
 *
 * @author mnaaf
 *
 */
public class CpxWeightedTrsRenamingProcessor extends CpxWeightedTrsProcessor {

    @Override
    protected boolean isCpxWeightedTrsApplicable(CpxWeightedTrsProblem obl) {
        return obl.getDefinedSymbols().stream().anyMatch(fun -> hasPredefinedName(fun));
    }

    @Override
    protected Result processCpxWeightedTrs(CpxWeightedTrsProblem obl, Abortion aborter, RuntimeInformation rti) {
        CpxWeightedTrsRenamingWorker worker = new CpxWeightedTrsRenamingWorker();
        Result res = worker.processCpxWeightedTrs(obl, aborter, rti);
        return res;
    }

    /**
     * @param obl the obligation in which the predefined symbols are to be
     *  renamed; non-null
     * @param aborter for multi-threaded abort request checks; non-null
     * @return a pair with x-component the renamed problem,
     *  y-component the mapping from old to new symbols (where changed), and
     *  z-component the mapping from old to new rules
     */
    public Pair<CpxWeightedTrsProblem,
            Map<FunctionSymbol,FunctionSymbol>>
                rename(CpxWeightedTrsProblem obl, Abortion aborter) {
        CpxWeightedTrsRenamingWorker worker = new CpxWeightedTrsRenamingWorker();
        Pair<CpxWeightedTrsProblem, Map<FunctionSymbol,FunctionSymbol>> res = worker.rename(obl, aborter);
        return res;
    }

    //checks if fun has a name that is also used by a predefined symbol or integer
    //(this does not mean that fun is actually a predefined symbol)
    private static boolean hasPredefinedName(FunctionSymbol fun) {
        if (IDPPredefinedMap.DEFAULT_MAP.getUsedNames().contains(fun.getName())) {
            return true;
        } else {
            //check if fun is the name an integer value
            FunctionSymbol funConst = FunctionSymbol.create(fun.getName(), 0);
            return CpxIntTermHelper.isIntegerTerm(TRSTerm.createFunctionApplication(funConst));
        }
    }

    /**
     * Helper class to encapsulate the instance-dependent state of the
     * computation by the processor.
     */
    private static class CpxWeightedTrsRenamingWorker {
        private FreshNameGenerator fng = null;
        private Set<FunctionSymbol> defsyms = null;
        private Map<FunctionSymbol,FunctionSymbol> renaming = null;

        private TRSTerm renamePredefined(TRSTerm term, CpxWeightedTrsProblem trs) {
            if (term.isVariable()) {
                return term;
            } else {
                TRSFunctionApplication funapp = (TRSFunctionApplication)term;
                ArrayList<TRSTerm> newArgs = new ArrayList<>();
                for (TRSTerm arg : funapp.getArguments()) {
                    newArgs.add(renamePredefined(arg,trs));
                }
                //rename only defined symbols that are reserved (i.e. predefined)
                FunctionSymbol fun = funapp.getRootSymbol();
                if (trs.isDefined(fun) && hasPredefinedName(fun)) {
                    String base = fun.getName();
                    //rename predefined arithmetic (including integers)
                    String fresh = fng.getFreshName(base, true);
                    FunctionSymbol newfun = FunctionSymbol.create(fresh, funapp.getRootSymbol().getArity());
                    if (defsyms.contains(funapp.getRootSymbol())) {
                        this.defsyms.add(newfun);
                    }
                    this.renaming.put(fun,newfun);
                    return TRSTerm.createFunctionApplication(newfun, newArgs);
                }
                return TRSTerm.createFunctionApplication(funapp.getRootSymbol(), newArgs);
            }
        }

        private WeightedRule renamePredefined(WeightedRule rule, CpxWeightedTrsProblem trs) {
            TRSFunctionApplication lhs = (TRSFunctionApplication)renamePredefined(rule.getLeft(),trs);
            TRSTerm rhs = renamePredefined(rule.getRight(),trs);
            return WeightedRule.create(lhs, rhs, rule.getWeight());
        }

        /**
         * @param obl the obligation in which the predefined symbols are to be
         *  renamed; non-null
         * @param aborter for multi-threaded abort request checks; non-null
         * @return a pair with x-component the renamed problem,
         *  y-component the mapping from old to new symbols (where changed), and
         *  z-component the mapping from old to new rules
         */
        private Pair<CpxWeightedTrsProblem,
                    Map<FunctionSymbol,FunctionSymbol>>
                rename(CpxWeightedTrsProblem obl, Abortion aborter) {
            this.renaming = new LinkedHashMap<>();
            this.defsyms = new LinkedHashSet<>();
            this.defsyms.addAll(obl.getDefinedSymbols());

            this.fng = new FreshNameGenerator(IDPPredefinedMap.DEFAULT_MAP.getUsedNames(), FreshNameGenerator.FRIENDLYNAMES);
            this.fng.lockNames(obl.getUsedNames());

            LinkedHashSet<WeightedRule> newR = new LinkedHashSet<>();
            for (WeightedRule rule : obl.getRules()) {
                newR.add(renamePredefined(rule,obl));
                aborter.checkAbortion();
            }
            CpxWeightedTrsProblem res = CpxWeightedTrsProblem.create(ImmutableCreator.create(newR), obl.isInnermost());
            return new Pair<>(res, this.renaming);
        }

        protected Result processCpxWeightedTrs(CpxWeightedTrsProblem obl, Abortion aborter, RuntimeInformation rti) {
            Pair<CpxWeightedTrsProblem, Map<FunctionSymbol,FunctionSymbol>>
                resAndRenamings = rename(obl, aborter);
            CpxWeightedTrsProblem res = resAndRenamings.x;
            return ResultFactory.proved(res, BothBounds.create(), new CpxWeightedTrsRenamingProof(this.renaming));
        }
    }

    private static class CpxWeightedTrsRenamingProof extends CpxProof {
        private Map<FunctionSymbol,FunctionSymbol> subs;

        public CpxWeightedTrsRenamingProof(final Map<FunctionSymbol,FunctionSymbol> subs) {
            this.subs = subs;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append(o.escape("Renamed defined symbols to avoid conflicts with arithmetic symbols:") + o.paragraph());
            subs.forEach((k,v) ->
                s.append(o.indent(k.export(o) + o.escape(" => ") + v.export(o) + o.linebreak()))
            );
            return s.toString();
        }
    }

}
