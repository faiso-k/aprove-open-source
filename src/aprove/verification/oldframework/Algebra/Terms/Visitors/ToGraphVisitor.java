package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.Graph.*;

/** Converts a Term into a Graph.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class ToGraphVisitor implements CoarseGrainedTermVisitor<Node<String>> {

    Graph<String,Object> g = new Graph<String,Object>();

    private String format(Symbol sym) {
        String[] parts = sym.getClass().getName().split("\\.");
        return sym.getName()+" :: "+parts[parts.length-1].split("Symbol")[0];
    }

    @Override
    public Node<String> caseVariable(AlgebraVariable v) {
        Node<String> node = new Node<String>(this.format(v.getSymbol()));
        this.g.addNode(node);
        return node;
    }

    @Override
    public Node<String> caseFunctionApp(AlgebraFunctionApplication fapp) {
        Node<String> from = new Node<String>(this.format(fapp.getSymbol()));
        Iterator i = fapp.getArguments().iterator();
        while (i.hasNext()) {
            AlgebraTerm arg = (AlgebraTerm)i.next();
            Node<String> to = arg.apply(this);
            this.g.addEdge(from, to);
        }
        return from;
    }

    public static Graph apply(AlgebraTerm t) {
        ToGraphVisitor gv = new ToGraphVisitor();
        t.apply(gv);
        return gv.g;
    }

}
