package aprove.input.Programs.prolog.processors.toirswt;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

class NodeToTermConverter {

    public TRSFunctionApplication getInSymbol(Node<PrologAbstractState> node) {
        return this.getNodeSymbol("f" + node.getNodeNumber() + "_in", node);
    }

    public TRSFunctionApplication getOutSymbol(Node<PrologAbstractState> node) {
        return this.getNodeSymbol("f" + node.getNodeNumber() + "_out", node);
    }

    private TRSFunctionApplication getNodeSymbol(String symbolName, Node<PrologAbstractState> node) {
        final Collection<TRSTerm> args = new LinkedList<>();
        for(PrologVariable variable : node.getObject().createSetOfAllVariables()) {
            if(node.getObject().getKnowledgeBase().isGround(variable)) {
                args.add(variable.toTerm());
            }
        }
        final FunctionSymbol symbol = FunctionSymbol.create(symbolName, args.size());
        return TRSTerm.createFunctionApplication(symbol, args.toArray(new TRSTerm[args.size()]));
    }

}
