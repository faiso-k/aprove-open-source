package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Extends the ToLaTeXVisitor, enabling it to highlight symbols in a given set<
 * @author Christian Kaeunicke
 * @version $Id$
 */
public class ToHighlightedVariablesLaTeXVisitor extends ToLaTeXVisitor {
    protected Set<VariableSymbol> importantSymbols;

    public ToHighlightedVariablesLaTeXVisitor(Set<VariableSymbol> set) {
    this.importantSymbols = set;
    };

    @Override
    public Object caseVariable(AlgebraVariable v) {
    if (this.importantSymbols.contains(v.getSymbol())) {
        return "\\textbf{" + ToLaTeXVisitor.escape(v.getName()) + "}";
    } else {
        return ToLaTeXVisitor.escape(v.getName());
    }
    }
}
