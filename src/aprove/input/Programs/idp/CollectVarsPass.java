package aprove.input.Programs.idp;

import java.util.*;

import aprove.input.Generated.idp.analysis.*;
import aprove.input.Generated.idp.node.*;

/**
 * Treewalker which collects all names declared in "VAR" sections
 * in an IDP input file.
 *
 * @author noschinski
 * @version $Id$
 */
public class CollectVarsPass extends DepthFirstAdapter {
    /**
     * remember if we are in a variable declaration
     */
    private boolean inVarDecl;
    /**
     * Collected variables
     */
    private Set<String> vars;

    public CollectVarsPass() {
        this.inVarDecl = false;
        this.vars = new LinkedHashSet<String>();
    }

    @Override
    public void inAVarlist(AVarlist node)
    {
        this.inVarDecl = true;
    }

    @Override
    public void outAVarlist(AVarlist node)
    {
        this.inVarDecl = false;
    }

    @Override
    public void inAVar(AVar node)
    {
        if(this.inVarDecl) {
            String name = node.getName().toString().trim();
            this.vars.add(EscapeHandler.unescape(name));
        }
    }

    /**
     * Returns collected variables
     */
    public Set<String> getVariables() {
        return this.vars;
    }
}
