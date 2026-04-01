package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Returns all variable symbols contained in a Term.
 *  <p>
 *  Note: Changing the variables will change the term's variables.
 * @author Burak Emir, Peter Schneider-Kamp, Christian Kaeuicke
 * @version $Id$
 */
public class GetVariableSymbolsVisitor extends CoarseGrainedDepthFirstTermVisitor {

    protected Collection<VariableSymbol> varSymbols;

    @Override
    public void inVariable(AlgebraVariable v) {
        this.varSymbols.add(v.getVariableSymbol());
    }

    protected GetVariableSymbolsVisitor(boolean isSet) {
        if (isSet) {
            this.varSymbols = new LinkedHashSet<VariableSymbol>();
        } else {
            this.varSymbols = new Vector<VariableSymbol>();
        }
    }

    public static Collection<VariableSymbol> apply(AlgebraTerm t, boolean isSet) {
        GetVariableSymbolsVisitor v = new GetVariableSymbolsVisitor(isSet);
        t.apply(v);
        return v.varSymbols;
    }
}
