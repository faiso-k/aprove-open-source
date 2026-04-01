package aprove.verification.oldframework.Utility.Profiling;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Utility.Profiling.Utility.*;
import aprove.verification.oldframework.Utility.Profiling.Utility.TRSProperties.Properties;
import immutables.*;

/**
 *
 * @author Tim Enger
 */

public class FeaturesQTRS {

    public enum Features {
        RMaxArity, RAvgArity, RMaxDepthLeft, RMaxDepthRight,
        RMaxDistinctVarsInRule, RMaxDuplicatingFactor,
        RMaxNonLinearityDegreeLeft, RMaxNonLinearityDegreeRight,
        RNumDifferentSymbols, RNumOfRules, RSize, RNumOfDifferentSubterms,
        RNumOfDefinedSymbols, RNumOfRhsEmbedLhs,
        RNumOfOccurFunctionSymbols, RNumOfOccurVariables,
        RMaxOccurFunctionSymbol, NumOfCollapsingRules
    }

    public static FeatureVector<Features> getFeatures(QTRSProblem qtrs) {
        LinkedHashMap<Features, Integer> map =
            new LinkedHashMap<Features, Integer>();

        ImmutableSet<Rule> r = qtrs.getR();
        EnumMap<Properties, Integer> rProps =
            TRSProperties.computeProperties(r);

        for (Map.Entry<Properties, Integer> e : rProps.entrySet()) {
            Integer value = e.getValue();
            switch (e.getKey()) {
            case MaxArity:
                map.put(Features.RMaxArity, value);
                break;
            case MaxDepthLeft:
                map.put(Features.RMaxDepthLeft, value);
                break;
            case MaxDepthRight:
                map.put(Features.RMaxDepthRight, value);
                break;
            case MaxDistinctVarsInRule:
                map.put(Features.RMaxDistinctVarsInRule, value);
                break;
            case MaxDuplicatingFactor:
                map.put(Features.RMaxDuplicatingFactor, value);
                break;
            case MaxNonLinearityDegreeLeft:
                map.put(Features.RMaxNonLinearityDegreeLeft, value);
                break;
            case MaxNonLinearityDegreeRight:
                map.put(Features.RMaxNonLinearityDegreeRight, value);
                break;
            case NumOfDifferentSymbols:
                map.put(Features.RNumDifferentSymbols, value);
                break;
            case NumOfRules:
                map.put(Features.RNumOfRules, value);
                break;
            case Size:
                map.put(Features.RSize, value);
                break;
            case NumOfDifferentSubterms:
                map.put(Features.RNumOfDifferentSubterms, value);
                break;
            case NumOfDefinedSyms:
                map.put(Features.RNumOfDefinedSymbols, value);
                break;
            case NumOfRhsEmbedLhs:
                map.put(Features.RNumOfRhsEmbedLhs, value);
                break;
            case NumOfOccurFunctionSymbols:
                map.put(Features.RNumOfOccurFunctionSymbols, value);
                break;
            case NumOfOccurVariables:
                map.put(Features.RNumOfOccurVariables, value);
                break;
            case AvgArity:
                map.put(Features.RAvgArity, value);
                break;
            case MaxOccurFunctionSymbol:
                map.put(Features.RMaxOccurFunctionSymbol, value);
                break;
            }
        }

        map.put(Features.NumOfCollapsingRules, qtrs.getCollapsingRules().size());

        return new FeatureVector<Features>("QTRS",
            new EnumMap<Features, Integer>(map));
    }
}


