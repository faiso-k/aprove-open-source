package aprove.verification.oldframework.Utility.Profiling;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Profiling.Utility.*;
import immutables.*;

/**
 * @author Tim Enger
 */

public class FeaturesQDP {

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
        QSuperR, Minimal, NumUsableRules,
        PNumOfOccurFunctionSymbols, RNumOfOccurFunctionSymbols,
        PRNumOfOccurFunctionSymbols, PNumOfOccurVariables,
        RNumOfOccurVariables, PRNumOfOccurVariables,
        PAvgArity, RAvgArity, PRAvgArity,
        PMaxOccurFunctionSymbol, RMaxOccurFunctionSymbol, PRMaxOccurFunctionSymbol,

        /** Graph Properties **/
        GMaxOutgoingEdges, GAvgOutgoingEdges, GSize, GOrder, GEdgeConnectivity
    }

    public static FeatureVector<Features> getFeatures(QDPProblem qdp) {
        LinkedHashMap<Features, Integer> map =
            new LinkedHashMap<Features, Integer>();

        ImmutableSet<Rule> p = qdp.getP();
        EnumMap<TRSProperties.Properties, Integer> pProps =
            TRSProperties.computeProperties(p);

        for (Map.Entry<TRSProperties.Properties, Integer> e : pProps.entrySet()) {
            Integer value = e.getValue();
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

        ImmutableSet<Rule> r = qdp.getR();
        EnumMap<TRSProperties.Properties, Integer> rProps =
            TRSProperties.computeProperties(r);

        for (Map.Entry<TRSProperties.Properties, Integer> e : rProps.entrySet()) {
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

        EnumMap<TRSProperties.Properties, Integer> prProps =
            TRSProperties.computeProperties(IterableConcatenator.create(p, r));

        for (Map.Entry<TRSProperties.Properties, Integer> e : prProps.entrySet()) {
            Integer value = e.getValue();
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

        map.put(Features.QSuperR, qdp.QsupersetOfLhsR() ? 1 : 0);
        map.put(Features.Minimal, qdp.getMinimal() ? 1 : 0);
        map.put(Features.NumUsableRules, qdp.getUsableRules().size());

        EnumMap<QDGraphProperties.Properties, Integer> graphProps =
            QDGraphProperties.computeProperties(qdp.getDependencyGraph());

        for (Map.Entry<QDGraphProperties.Properties, Integer> e : graphProps.entrySet()) {
            Integer value = e.getValue();
            switch (e.getKey()) {
            case AvgOutgoingEdges:
                map.put(Features.GAvgOutgoingEdges, value);
                break;
            case EdgeConnectivity:
                map.put(Features.GEdgeConnectivity, value);
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

        return new FeatureVector<Features>("QDP",
            new EnumMap<Features, Integer>(map));
    }
}
