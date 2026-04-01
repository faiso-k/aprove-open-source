package aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.CpxIntTrsToKoATProcessor.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Bytecode.Processors.ToComplexity.*;
import aprove.verification.oldframework.WeightedIntTrs.*;

public class WeightedIntTrsToKoATLikeBackendForMethodSummaryProcessor
        extends WeightedIntTrsToKoATLikeBackendProcessor<CpxIntTrsToKoATProcessor.Arguments, CpxIntTrsToKoATProcessor> {
    
    public WeightedIntTrsToKoATLikeBackendForMethodSummaryProcessor() {
        this(new CpxIntTrsToKoATProcessor.Arguments());
    }

    @ParamsViaArgumentObject
    WeightedIntTrsToKoATLikeBackendForMethodSummaryProcessor(Arguments args) {
        super(new CpxIntTrsToKoATProcessor(args));
    }
    
    @Override
    protected Result onKoatFail(WeightedIntTrs obl, KoatException e) {
        ((WeightedIntTrsForMethodSummary)obl).getTask().fail(e);
        return super.onKoatFail(obl, e);
    }

    @Override
    protected Result onKoatSucces(WeightedIntTrs obl, String result, List<String> proof) {
        WeightedIntTrsForMethodSummary summaryIts = (WeightedIntTrsForMethodSummary) obl;
        Map<String, String> polyReplaceMap = new LinkedHashMap<>();
        for (Map.Entry<Integer, ComplexityGoalTerm> entry : summaryIts.getStartTermArgMap().entrySet()) {
            polyReplaceMap.put("Ar_" + entry.getKey(), entry.getValue().getStringRepresentation());
            polyReplaceMap.put("ar_" + entry.getKey(), entry.getValue().getStringRepresentation());
        }
        MethodSummaryBuilder.Task task = summaryIts.getTask();
        try {
            SimplePolynomial poly = KoATParser.parseAsPolynomial(result).replace(polyReplaceMap);
            task.finish(poly);
            proof.add("");
            proof.add("Method Summary task finished: " + task + ", Size: " + poly);
        } catch (KoATParser.NonConstantExponentException e) {
            task.fail(e);
        }
        return super.onKoatSucces(obl, result, proof);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return super.isApplicable(obl) && obl instanceof WeightedIntTrsForMethodSummary;
    }
    
}
