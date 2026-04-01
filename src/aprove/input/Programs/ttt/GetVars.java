package aprove.input.Programs.ttt;

import java.util.*;

import aprove.input.Generated.ttt.node.*;
import aprove.verification.oldframework.Syntax.*;

/** Treewalker that collects all variable symbols of the
 *  term rewriting system.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

class GetVars extends Pass {

    private Hashtable vars = new Hashtable();

    @Override
    public void inAConstVarPrefixterm(AConstVarPrefixterm node) {
    String name = this.chop(node.getId());
        try {
            Integer.parseInt(name);
        }
        catch (NumberFormatException e) {
            this.gvars.add(name);
            this.vars.put(name, VariableSymbol.create(name, this.poly));
        }
    }

    public Map getTermVars() {
        return this.vars;
    }

}
