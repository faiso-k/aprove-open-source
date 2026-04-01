package aprove.input.Programs.srs;

import java.util.*;

import aprove.input.Generated.srs.node.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Treewalker that implements the first pass of
 *  the AST conversion.
 *  <p>
 *  This pass basically just picks up all defined functions.
 * @author Peter Schneider-Kamp, Stephan Falke
 * @version $Id$
 */

class Pass1 extends Pass {

    @Override
    public void inARule(ARule node) {
    Token t = (Token)node.getLeft();
    String name = ""+this.chop(t).charAt(0);
        DefFunctionSymbol f;
        f = this.prog.getDefFunctionSymbol(name);
        if (f == null) {
            f = DefFunctionSymbol.create(name, new Vector<Sort>(), this.poly);
            f.addArgSort(this.poly);
            try {
                this.prog.addDefFunctionSymbol(f);
                this.prog.setFunctionSignature(f, Symbol.MAINSIG);
            } catch (ProgramException e) {}
        }
    }

}
