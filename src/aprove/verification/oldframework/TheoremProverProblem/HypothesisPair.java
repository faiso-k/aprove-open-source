package aprove.verification.oldframework.TheoremProverProblem;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Just a pair of a formula and its allquantified variables
 *
 * @version $Id$
 */

public class HypothesisPair extends Pair<Formula, Set<VariableSymbol>>
        implements HTML_Able, LaTeX_Able, PLAIN_Able {

    public HypothesisPair(Formula x, Set<VariableSymbol> y) {
        super(x, y);
    }

    public HypothesisPair(Pair<Formula, Set<VariableSymbol>> pair) {
        super(pair.x, pair.y);
    }

    @Override
    public String toLaTeX() {
        return ToLaTeXVisitor.apply(this.x, this.y);
    }

    @Override
    public String toHTML() {
        return ToHTMLFormulaVisitor.apply(this.x, this.y);
    }

    @Override
    public String toPLAIN() {
        return ToASCIIFormulaVisitor.apply(this.x, this.y);
    }

}