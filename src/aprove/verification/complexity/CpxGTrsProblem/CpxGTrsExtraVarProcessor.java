package aprove.verification.complexity.CpxGTrsProblem;

import static aprove.verification.oldframework.Utility.Collection_Util.*;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

public class CpxGTrsExtraVarProcessor extends ProcessorSkeleton {

    boolean isBasic(TRSFunctionApplication t, Set<FunctionSymbol> definedSymbols) {
        return definedSymbols.contains(t.getRootSymbol()) && t.getArguments().stream().allMatch(s -> areDisjoint(definedSymbols, s.getFunctionSymbols()));
    }

    class ExtraVarProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "unbounded runtime complexity due to extra variable on rhs";
        }

    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        CpxGTrsProblem cpxTrs = (CpxGTrsProblem) obl;
        Set<FunctionSymbol> definedSymbols = cpxTrs.getDefinedSymbols();
        for (GeneralizedRule r: cpxTrs.getRules()) {
            if (isBasic(r.getLeft(), definedSymbols) && !r.getLeft().getVariables().containsAll(r.getRight().getVariables())) {
                return ResultFactory.provedWithValue(ComplexityYNM.INFINITE, new ExtraVarProof());
            }
        }
        return ResultFactory.unsuccessful();
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return Options.certifier == Certifier.NONE && obl instanceof CpxGTrsProblem;
    }

}
