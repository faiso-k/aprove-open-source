package aprove.verification.oldframework.Utility.Profiling;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Profiling.Utility.*;
import aprove.verification.oldframework.Utility.Profiling.Utility.TRSProperties.Properties;
import immutables.*;

/**
 * @author Tim Enger
 */

public class FeaturesIDP {

    public enum Features {
        PMaxArity, PMaxDepthLeft, PMaxDepthRight, PMaxDistinctVarsInRule,
        PMaxDuplicatingFactor, PMaxNonLinearityDegreeLeft,
        PMaxNonLinearityDegreeRight, PNumDifferentSymbols, PNumOfRules, PSize,
        PNumOfDifferentSubterms, PNumOfDefinedSymbols, RMaxArity,
        RMaxDepthLeft, RMaxDepthRight, RMaxDistinctVarsInRule,
        RMaxDuplicatingFactor, RMaxNonLinearityDegreeLeft,
        RMaxNonLinearityDegreeRight, RNumDifferentSymbols, RNumOfRules, RSize,
        RNumOfDifferentSubterms, RNumOfDefinedSymbols, PRMaxArity,
        PRMaxDepthLeft, PRMaxDepthRight, PRMaxDistinctVarsInRule,
        PRMaxDuplicatingFactor, PRMaxNonLinearityDegreeLeft,
        PRMaxNonLinearityDegreeRight, PRNumDifferentSymbols, PRNumOfRules,
        PRSize, PRNumOfDifferentSubterms, PRNumOfDefinedSymbols,
        PNumOfRhsEmbedLhs, RNumOfRhsEmbedLhs, PRNumOfRhsEmbedLhs,
        PNumOfOccurFunctionSymbols, RNumOfOccurFunctionSymbols,
        PRNumOfOccurFunctionSymbols, PNumOfOccurVariables,
        RNumOfOccurVariables, PRNumOfOccurVariables,
        PAvgArity, RAvgArity, PRAvgArity,
        PMaxOccurFunctionSymbol, RMaxOccurFunctionSymbol, PRMaxOccurFunctionSymbol,

        /** Graph Properties **/
        GMaxOutgoingEdges, GAvgOutgoingEdges, GSize, GOrder,

        /** Predefined Functions Properties **/
        NumOfAdd, NumOfSub, NumOfMul, NumOfDiv, NumOfLAnd, NumOfLOr, NumOfLNot,
    }

    public static FeatureVector<Features> getFeatures(final IDPProblem idp) {
        final LinkedHashMap<Features, Integer> map =
            new LinkedHashMap<Features, Integer>();

        final ImmutableSet<GeneralizedRule> p = idp.getP();
        final EnumMap<Properties, Integer> pProps =
            TRSProperties.computeProperties(p);

        for (final Map.Entry<Properties, Integer> e : pProps.entrySet()) {
            final Integer value = e.getValue();
            switch (e.getKey()) {
            case MaxArity:
                map.put(Features.PMaxArity, value);
                break;
            case MaxDepthLeft:
                map.put(Features.PMaxDepthLeft, value);
                break;
            case MaxDepthRight:
                map.put(Features.PMaxDepthRight, value);
                break;
            case MaxDistinctVarsInRule:
                map.put(Features.PMaxDistinctVarsInRule, value);
                break;
            case MaxDuplicatingFactor:
                map.put(Features.PMaxDuplicatingFactor, value);
                break;
            case MaxNonLinearityDegreeLeft:
                map.put(Features.PMaxNonLinearityDegreeLeft, value);
                break;
            case MaxNonLinearityDegreeRight:
                map.put(Features.PMaxNonLinearityDegreeRight, value);
                break;
            case NumOfDifferentSymbols:
                map.put(Features.PNumDifferentSymbols, value);
                break;
            case NumOfRules:
                map.put(Features.PNumOfRules, value);
                break;
            case Size:
                map.put(Features.PSize, value);
                break;
            case NumOfDifferentSubterms:
                map.put(Features.PNumOfDifferentSubterms, value);
                break;
            case NumOfDefinedSyms:
                map.put(Features.PNumOfDefinedSymbols, value);
                break;
            case NumOfRhsEmbedLhs:
                map.put(Features.PNumOfRhsEmbedLhs, value);
                break;
            case NumOfOccurFunctionSymbols:
                map.put(Features.PNumOfOccurFunctionSymbols, value);
                break;
            case NumOfOccurVariables:
                map.put(Features.PNumOfOccurVariables, value);
                break;
            case AvgArity:
                map.put(Features.PAvgArity, value);
                break;
            case MaxOccurFunctionSymbol:
                map.put(Features.PMaxOccurFunctionSymbol, value);
                break;
            }
        }

        final ImmutableSet<GeneralizedRule> r = idp.getR();
        final EnumMap<Properties, Integer> rProps =
            TRSProperties.computeProperties(r);

        for (final Map.Entry<Properties, Integer> e : rProps.entrySet()) {
            final Integer value = e.getValue();
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

        final EnumMap<Properties, Integer> prProps =
            TRSProperties.computeProperties(IterableConcatenator.create(p, r));

        for (final Map.Entry<Properties, Integer> e : prProps.entrySet()) {
            final Integer value = e.getValue();
            switch (e.getKey()) {
            case MaxArity:
                map.put(Features.PRMaxArity, value);
                break;
            case MaxDepthLeft:
                map.put(Features.PRMaxDepthLeft, value);
                break;
            case MaxDepthRight:
                map.put(Features.PRMaxDepthRight, value);
                break;
            case MaxDistinctVarsInRule:
                map.put(Features.PRMaxDistinctVarsInRule, value);
                break;
            case MaxDuplicatingFactor:
                map.put(Features.PRMaxDuplicatingFactor, value);
                break;
            case MaxNonLinearityDegreeLeft:
                map.put(Features.PRMaxNonLinearityDegreeLeft, value);
                break;
            case MaxNonLinearityDegreeRight:
                map.put(Features.PRMaxNonLinearityDegreeRight, value);
                break;
            case NumOfDifferentSymbols:
                map.put(Features.PRNumDifferentSymbols, value);
                break;
            case NumOfRules:
                map.put(Features.PRNumOfRules, value);
                break;
            case Size:
                map.put(Features.PRSize, value);
                break;
            case NumOfDifferentSubterms:
                map.put(Features.PRNumOfDifferentSubterms, value);
                break;
            case NumOfDefinedSyms:
                map.put(Features.PRNumOfDefinedSymbols, value);
                break;
            case NumOfRhsEmbedLhs:
                map.put(Features.PRNumOfRhsEmbedLhs, value);
                break;
            case NumOfOccurFunctionSymbols:
                map.put(Features.PRNumOfOccurFunctionSymbols, value);
                break;
            case NumOfOccurVariables:
                map.put(Features.PRNumOfOccurVariables, value);
                break;
            case AvgArity:
                map.put(Features.PRAvgArity, value);
                break;
            case MaxOccurFunctionSymbol:
                map.put(Features.PRMaxOccurFunctionSymbol, value);
                break;
            }
        }

        final EnumMap<IDGraphProperties.Properties, Integer> graphProps =
            IDGraphProperties.computeProperties(idp.getIdpGraph());

        for (final Map.Entry<IDGraphProperties.Properties, Integer> e : graphProps.entrySet()) {
            final Integer value = e.getValue();
            switch (e.getKey()) {
            case AvgOutgoingEdges:
                map.put(Features.GAvgOutgoingEdges, value);
                break;
            case MaxOutgoingEdges:
                map.put(Features.GMaxOutgoingEdges, value);
                break;
            case Order:
                map.put(Features.GOrder, value);
                break;
            case Size:
                map.put(Features.GSize, value);
                break;
            }
        }

        final Map<Features, Integer> predefinedPropertied = FeaturesIDP.computePredefinedPropertied(idp);
        map.putAll(predefinedPropertied);

        return new FeatureVector<Features>("IDP",
            new EnumMap<Features, Integer>(map));
    }

    private static Map<Features, Integer> computePredefinedPropertied(final IDPProblem idp) {
        final LinkedHashMap<Features, Integer> res = new LinkedHashMap<Features, Integer>();

        final IDPPredefinedMap predefinedMap = idp.getRuleAnalysis().getPreDefinedMap();

        final ImmutableCollection<FunctionSymbol> predefinedFunctions = predefinedMap.getPredefinedFunctionSymbols();

        FeaturesIDP.countPredefinedFunctions(res, idp.getR(), predefinedFunctions, predefinedMap);
        FeaturesIDP.countPredefinedFunctions(res, idp.getP(), predefinedFunctions, predefinedMap);

        return res;
    }

    private static void countPredefinedFunctions(final LinkedHashMap<Features, Integer> res,
        final ImmutableSet<GeneralizedRule> rules,
        final ImmutableCollection<FunctionSymbol> predefinedFunctions, final IDPPredefinedMap predefinedMap) {
        for (final GeneralizedRule r : rules) {
            final Map<FunctionSymbol, Integer> fsCount = r.getRight().getFunctionSymbolCount();
            fsCount.keySet().retainAll(predefinedFunctions);

            for (final Map.Entry<FunctionSymbol, Integer> predefinedCount : fsCount.entrySet()) {
                Features feature = null;
                switch (predefinedMap.getPredefinedFunction(predefinedCount.getKey()).getFunc()) {
                case Add:
                    feature = Features.NumOfAdd; break;
                case Sub:
                    feature = Features.NumOfSub; break;
                case Mul:
                    feature = Features.NumOfMul; break;
                case Div:
                    feature = Features.NumOfDiv; break;
                case Land:
                    feature = Features.NumOfLAnd; break;
                case Lor:
                    feature = Features.NumOfLOr; break;
                case Lnot:
                    feature = Features.NumOfLNot; break;
                }

                if (feature != null) {
                    FeaturesIDP.addToMap(res, feature, predefinedCount.getValue());
                }
            }
        }
        // make sure that every features is contained in a hacky way. hi martin.
        FeaturesIDP.addToMap(res, Features.NumOfAdd, 0);
        FeaturesIDP.addToMap(res, Features.NumOfSub, 0);
        FeaturesIDP.addToMap(res, Features.NumOfMul, 0);
        FeaturesIDP.addToMap(res, Features.NumOfDiv, 0);
        FeaturesIDP.addToMap(res, Features.NumOfLAnd, 0);
        FeaturesIDP.addToMap(res, Features.NumOfLOr, 0);
        FeaturesIDP.addToMap(res, Features.NumOfLNot, 0);
    }

    private static void addToMap(final LinkedHashMap<Features, Integer> map,
        final Features feature,
        final Integer count) {
        final Integer oldCount = map.get(feature);
        if (oldCount != null) {
            map.put(feature, oldCount + count);
        } else {
            map.put(feature, count);
        }
    }

}
