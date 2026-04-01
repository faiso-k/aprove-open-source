package aprove.input.Programs.ttt;

import aprove.input.Generated.ttt.node.*;
import aprove.input.Utility.*;

/**
 * Treewalker that checks some stuff.
 * <p>
 * @author Stephan Falke
 * @version $Id$
 */

class Pass0 extends Pass {

    private boolean hasTheories = false;
    private boolean hasConditions = false;

    @Override
    public void inASimple(ASimple node) {
        if (!this.chop(node.getArrow()).equals("==")) {
            // it's a rule
            return;
        }
        if (this.hasConditions) {
            this.addParseError(node.getArrow(), ParseError.ERROR, "conditional equational rewriting not yet supported");
        }
        this.hasTheories = true;
    }

    @Override
    public void inAConditional(AConditional node) {
        if (this.hasTheories) {
        this.addParseError(node.getPipe(), ParseError.ERROR, "conditional equational rewriting not yet supported");
        }
        this.hasConditions = true;
    }

}
