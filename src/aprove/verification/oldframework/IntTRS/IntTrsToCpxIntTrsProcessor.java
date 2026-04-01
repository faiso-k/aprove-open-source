package aprove.verification.oldframework.IntTRS;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class IntTrsToCpxIntTrsProcessor extends Processor.ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        IRSLike irs = (IRSLike) obl;
        LinkedHashSet<CpxIntTupleRule> res = new LinkedHashSet<>();
        for (IGeneralizedRule r: irs.getRules()) {
            try {
                res.addAll(CpxIntTupleRule.createRules(r));
            } catch (NoValidCpxIntTupleRuleException e) {
                e.printStackTrace();
                return ResultFactory.unsuccessful();
            }
        }
        LinkedHashSet<FunctionSymbol> startSymbol = new LinkedHashSet<>();
        startSymbol.add(irs.getStartTerm().getRootSymbol());
        CpxIntTrsProblem cint = CpxIntTrsProblem.create(ImmutableCreator.create(res), ImmutableCreator.create(startSymbol));
        return ResultFactory.proved(cint, UpperBound.create(), new IRSToCpxIntTrsProof());
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (!(obl instanceof IRSLike)) {
            return false;
        }
        IRSLike irs = (IRSLike) obl;
        return irs.getStartTerm() != null;
    }

    private class IRSToCpxIntTrsProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("transformed IRS to CpxIntTrs");
        }

    }
}
