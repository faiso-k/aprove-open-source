package aprove.input.Programs.ttt;

import java.util.*;

import aprove.input.Generated.ttt.node.*;
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
    public void inASimple(ASimple node) {
        if (this.cond) {return;}
        if (this.chop(node.getArrow()).equals("==")) {return;}
    PTerm p = node.getLeft();
    Token t = null;
        boolean var = false;
    boolean infix = false;
    if (p instanceof APrefixTerm) {
        PPrefixterm pp = ((APrefixTerm)p).getPrefixterm();
        if (pp instanceof AFunctAppPrefixterm) {
            t = ((AFunctAppPrefixterm)pp).getId();
        } else if (pp instanceof AConstVarPrefixterm) {
            t = ((AConstVarPrefixterm)pp).getId();
                var = true;
        }
    } else if (p instanceof AInfixTerm) {
        infix = true;
        PInfixterm pp = ((AInfixTerm)p).getInfixterm();
        if (pp instanceof AIninInfixterm) {
            t = ((AIninInfixterm)pp).getInfixid();
        } else if (pp instanceof AInpreInfixterm) {
            t = ((AInpreInfixterm)pp).getInfixid();
        } else if (pp instanceof APreinInfixterm) {
            t = ((APreinInfixterm)pp).getInfixid();
        } else if (pp instanceof APrepreInfixterm) {
            t = ((APrepreInfixterm)pp).getInfixid();
        }
    }
        String name = this.chop(t);
        try {
            if (var && Integer.parseInt(name) != -1) {
                var = false;
            }
        } catch (NumberFormatException e) {
            this.gvars.add(name);
        }
        if (!var) {
        DefFunctionSymbol f;
        int arity = 0;
        if(!infix) {
            PPrefixterm pp = ((APrefixTerm)p).getPrefixterm();
            if (pp instanceof AFunctAppPrefixterm) {
                    ATermlist termlist = ((ATermlist)((AFunctAppPrefixterm)pp).getTermlist());
                    if (termlist != null) {
                        arity = termlist.getTermcomma().size()+1;
                    }
        }
        }
        else {
        /* infix operators are binary */
        arity = 2;
        //name = escape(name);
        }
        f = this.prog.getDefFunctionSymbol(name);
        if (f == null) {
        f = DefFunctionSymbol.create(name, new Vector<Sort>(), this.poly);
        for (int i=0; i<arity; i++) {
            f.addArgSort(this.poly);
        }
        if(infix) {
            f.setFixity(SyntacticFunctionSymbol.INFIX);
        }
        try {this.prog.addDefFunctionSymbol(f);} catch (ProgramException e) {}
        } else if (f.getArity() != arity) {
        this.addParseError(t, "arity "+Integer.valueOf(f.getArity()).toString()+" expected for function symbol '"+name+"', not "+Integer.valueOf(arity).toString());
        }
    } else {
        this.addParseError(t, "defining function expected, not variable '"+name+"'");
    }
    }

}
