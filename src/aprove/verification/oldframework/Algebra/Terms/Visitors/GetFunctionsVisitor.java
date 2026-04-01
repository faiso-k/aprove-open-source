package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Returns all function symbols contained in a Term.
 * @author Burak Emir, Peter Schneider-Kamp
 * @version $Id$
 */

public class GetFunctionsVisitor extends CoarseGrainedDepthFirstTermVisitor {

    protected Set<SyntacticFunctionSymbol> funcs;

    @Override
    public void inFunctionApp(AlgebraFunctionApplication f) {
    this.funcs.add((SyntacticFunctionSymbol) f.getSymbol());
    }

    protected GetFunctionsVisitor() {
    this.funcs = new LinkedHashSet<SyntacticFunctionSymbol>();
    }

    public static Set<SyntacticFunctionSymbol> apply(AlgebraTerm t) {
    GetFunctionsVisitor v = new GetFunctionsVisitor();
    t.apply(v);
    return v.funcs;
    }
}
