package aprove.input.Programs.llvm.segraph.edges;

import java.util.*;

import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Connects a return state in a recursive graph with possible calling states.
 * @author Frank
 */
public class LLVMContextConcretizationEdge  extends LLVMEdgeInformation {

    /**
     * A node at the beginning of the method.
     */
    private Node<LLVMAbstractState> concretinizedWithStartNode;


    public Node<LLVMAbstractState> getConcretinizedWithStartNode() {
        return this.concretinizedWithStartNode;
    }

    public LLVMContextConcretizationEdge(Node<LLVMAbstractState> concretinizedWithStartNode) {
        super(Collections.emptySet()); //TODO: Just a stub so far
        this.concretinizedWithStartNode = concretinizedWithStartNode;
    }

//    @Override
//    public Triple<TRSFunctionApplication, TRSFunctionApplication, TRSTerm>
//            applySubstitutionsToRuleTerms(TRSFunctionApplication startNodeTerm,
//                                          TRSFunctionApplication endNodeTerm,
//                                          TRSTerm conditionTerm) {
//        // TODO This is just a stub
//        return new Triple<>(startNodeTerm,endNodeTerm,conditionTerm);
//    }

    @Override
    public String getDotColor() {
        return "orange";
    }

//    @Override
//    public Term toRuleCondition(boolean useInvariantsOnInstanceEdges) {
//        Term superTerm = super.toRuleCondition(useInvariantsOnInstanceEdges);
//
//        FunctionSymbol land = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Land, DomainFactory.BOOLEAN);
//        FunctionSymbol eq = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Eq, DomainFactory.INTEGERS);
//        FunctionSymbol ge = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Ge, DomainFactory.INTEGERS);
//        FunctionSymbol minus = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Sub, DomainFactory.INTEGERS);
//        Term one = IDPPredefinedMap.DEFAULT_MAP.getIntTerm(BigIntImmutable.ONE, DomainFactory.INTEGERS);
//        Term zero = IDPPredefinedMap.DEFAULT_MAP.getIntTerm(BigIntImmutable.ZERO, DomainFactory.INTEGERS);
//        Term minusTerm = FunctionApplication.createFunctionApplication(minus, Term.createVariable("s"), one);
//
//        //We assume that the stack in the start node is called s and s2 in the end node.
//        Term stackRel = FunctionApplication.createFunctionApplication(eq, Term.createVariable("s2"),minusTerm);
//        Term greaterZero = FunctionApplication.createFunctionApplication(ge, Term.createVariable("s2"),zero);
//        Term wholeTerm =  FunctionApplication.createFunctionApplication(land, stackRel,greaterZero);
//        //stackRel should be "s2 == s - 1"
//        //greaterZero should be "s2 >= 0"
//
//        if(superTerm instanceof FunctionApplication &&
//                ((FunctionApplication) superTerm).getRootSymbol().equals(IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue().getSym())) {
//            return wholeTerm;
//        } else {
//            return FunctionApplication.createFunctionApplication(land, superTerm,wholeTerm);
//        }
//
//    };

    @Override
    public String getDotLabel() {
        final StringBuilder strBuilder = new StringBuilder();
        strBuilder.append("Context Concretinization \nWith node " + this.concretinizedWithStartNode.getNodeNumber());
        this.getDotLabel(strBuilder);
        return strBuilder.toString();
    }

}
