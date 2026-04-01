package aprove.verification.complexity.LowerBounds;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxRelTrsProblem.Processors.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

public class CpxTrsRenamingProcessor extends CpxRelTrsProcessor {

    /**
     * Helper class to encapsulate the instance-dependent state of the
     * computation by the processor.
     */
    private static class CpxTrsRenamingWorker {
        private Set<Rule> rules;
        private Set<Rule> relativeRules;
        private Set<Rule> renamedRules = new LinkedHashSet<>();
        private Set<Rule> renamedRelativeRules = new LinkedHashSet<>();
        private Set<FunctionSymbol> symbols;

        public Result process(BasicObligation obl) {
            assert obl instanceof CpxRelTrsProblem;
            CpxRelTrsProblem cpxRelTrs = (CpxRelTrsProblem)obl;
            rules = cpxRelTrs.getR();
            relativeRules = cpxRelTrs.getS();
            symbols = cpxRelTrs.getSignature();
            this.renameFunctionSymbols();
            BasicObligation newObl = cpxRelTrs.withRules(this.renamedRules, this.renamedRelativeRules);
            Result res = ResultFactory.proved(newObl, BothBounds.create(), new RenamingProof());
            return res;
        }

        private void renameFunctionSymbols() {
            Set<String> usedNames = new LinkedHashSet<>();
            usedNames.add(PFHelper.ADD.getName());
            usedNames.add(PFHelper.EQ.getName());
            usedNames.add(PFHelper.GE.getName());
            usedNames.add(PFHelper.ITE.getName());
            usedNames.add(PFHelper.MUL.getName());
            usedNames.add(PFHelper.FALSE.getSym().getName());
            usedNames.add(PFHelper.TRUE.getSym().getName());
            for (FunctionSymbol f: symbols) {
                boolean isInt = f.getArity() == 0 && PFHelper.isInt(TRSTerm.createFunctionApplication(f));
                if (isInt) {
                    usedNames.add(f.getName());
                }
            }
            FreshNameGenerator fng = new FreshNameGenerator(usedNames, FreshNameGenerator.VARIABLES);
            Map<FunctionSymbol, FunctionSymbol> renaming = new LinkedHashMap<>();
            for (FunctionSymbol f: symbols) {
                if (usedNames.contains(f.getName())) {
                    renaming.put(f, FunctionSymbol.create(fng.getFreshName(f.getName(), false), f.getArity()));
                }
            }
            for (Rule r : rules) {
                this.renamedRules.add(r.replaceAllFunctionSymbols(renaming));
            }
            for (Rule r : relativeRules) {
                this.renamedRelativeRules.add(r.replaceAllFunctionSymbols(renaming));
            }
        }

    }

    private static class RenamingProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("Renamed function symbols to avoid clashes with predefined symbol.");
        }

    }

    @Override
    protected Result processCpxRelTrs(CpxRelTrsProblem obl, Abortion aborter, RuntimeInformation rti) {
        CpxTrsRenamingWorker worker = new CpxTrsRenamingWorker();
        Result res = worker.process(obl);
        return res;
    }

    @Override
    protected boolean isCpxRelTrsApplicable(CpxRelTrsProblem obl) {
        return Options.certifier == Certifier.NONE;
    }

}
