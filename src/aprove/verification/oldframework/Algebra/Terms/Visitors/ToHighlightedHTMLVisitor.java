package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Converts a Term into a String highlighting symbols accoring to a colormap
 * which is currently a mapping of Symbols to Strings. The Strings will be used
 * as the COLOR attribute of the FONT tag
 * @author Christian Kaeunicke
 * @version $Id$
 */
public class ToHighlightedHTMLVisitor extends CustomizedToHTMLVisitor {

    public Map colorMap;

    public ToHighlightedHTMLVisitor(Map map) {
    this.colorMap = map;
    };

    private String calcColor(Symbol symbol) {
    String forReturn = (String) this.colorMap.get(symbol);
    if (forReturn == null) {
        forReturn = CustomizedToHTMLVisitor.defaultColor;
    }
    return forReturn;
    };

    @Override
    public String variableSymbolPrefix(AlgebraVariable v) {
    return "<FONT COLOR=" + this.calcColor(v.getSymbol()) + "><I>";
    }

    @Override
    public String variableSymbolPostfix(AlgebraVariable v) {
    return "</I></FONT>";
    };

    @Override
    public String constructorAppSymbolPrefix(ConstructorApp c) {
    return "<FONT COLOR=" + this.calcColor(c.getSymbol()) + ">";
    }

    @Override
    public String constructorAppSymbolPostfix(ConstructorApp c) {
    return "</FONT>";
    };

    @Override
    public String defFunctionAppSymbolPrefix(DefFunctionApp d) {
    return "<FONT COLOR=" + this.calcColor(d.getSymbol()) + ">";
    }

    @Override
    public String defFunctionAppSymbolPostfix(DefFunctionApp d) {
    return "</FONT>";
    };
}
