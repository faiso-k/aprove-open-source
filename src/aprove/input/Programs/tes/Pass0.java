package aprove.input.Programs.tes;

import aprove.input.Generated.tes.node.*;
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
        if (this.chop(node.getArrow()).equals("==")) {
            // it's an equation
            this.theo(node.getArrow());
        }
    }

    @Override
    public void inAAcdecl(AAcdecl acs) {
        this.theo(acs.getAc());
    }

    @Override
    public void inACdecl(ACdecl acs) {
        this.theo(acs.getC());
    }

    @Override
    public void inAAdecl(AAdecl acs) {
        this.theo(acs.getA());
    }

    public void theo(Token node) {
        if (this.hasConditions) {
            this.addParseError(node, ParseError.ERROR, "conditional equational rewriting not yet supported");
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
