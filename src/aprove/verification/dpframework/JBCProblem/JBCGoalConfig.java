package aprove.verification.dpframework.JBCProblem;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Input.*;

public class JBCGoalConfig {

    public String export(Export_Util o, HandlingMode goal, String programInformation) {
        StringBuilder sb = new StringBuilder();
        String str;
        switch (goal) {
            case SizeComplexity: str = "need to analyze the size complexity of";
            break;
            case SpaceComplexity: str = "need to analyze the space complexity of";
            break;
            case RuntimeComplexity: str = "need to analyze the time complexity of";
            break;
            case UserDefined: str= "need to analyze the complexity w.r.t. a user defined cost model of";
            break;
            case MethodSummary: str = "need to compute a method summary for";
            break;
            case Termination: str = "need to prove termination of";
            break;
            default: throw new RuntimeException();
        }
        sb
            .append(str)
            .append(" the following program:")
            .append(o.linebreak())
            .append(o.preFormatted(o.escape(programInformation.replace("\r", ""))));
        return sb.toString();
    }

    public ProofPurposeDescriptor getProofPurposeDescriptor(HandlingMode goal, BasicObligation obl) {
        switch (goal) {
            case SizeComplexity:
                return new ComplexityProofPurposeDescriptor(obl, "size complexity");
            case SpaceComplexity:
                return new ComplexityProofPurposeDescriptor(obl, "space complexity");
            case RuntimeComplexity:
                return new ComplexityProofPurposeDescriptor(obl, "time complexity");
            case UserDefined:
                return new ComplexityProofPurposeDescriptor(obl, "user defined cost model");
            case MethodSummary:
                return new MethodSummaryProofPurposeDescriptor();
            case Termination:
                return new DefaultProofPurposeDescriptor(obl, "termination");
            default: throw new RuntimeException();
        }
    }

    public String getStrategyName(HandlingMode goal) {
        switch (goal) {
            case Termination: return "jbcTerm";
            case RuntimeComplexity:
            case SizeComplexity:
            case UserDefined:
            case SpaceComplexity: return "jbcComplexity";
            case MethodSummary: return "jbcMethodSummary";
            default: throw new RuntimeException(goal + " not supported for jbc");
        }
    }

}
