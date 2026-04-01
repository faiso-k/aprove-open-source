package aprove.input.Programs.tes;

import java.util.*;

import aprove.input.Generated.tes.node.*;
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

    private boolean var;

    @Override
    public void inAVardecl(AVardecl node) {this.var = true;}
    @Override
    public void outAVardecl(AVardecl node) {this.var = false;}

    @Override
    public void inAIdcomma(AIdcomma node) {
    if(this.var) {
        this.checkandadd(node.getIdiid());
    }
    }

    @Override
    public void outAIdlist(AIdlist node) {
    if(this.var) {
        this.checkandadd(node.getIdiid());
    }
    }

    @Override
    public void inASimple(ASimple node) {
        if (this.cond) {return;}
        if (this.chop(node.getArrow()).equals("==")) {

        PTerm p = node.getRight();
        Token t = null;
        boolean infix = false;
        if (p instanceof APrefixTerm) {
        PPrefixterm pp = ((APrefixTerm)p).getPrefixterm();
        if (pp instanceof AFunctAppPrefixterm) {
            t = ((AFunctAppPrefixterm)pp).getId();
        } else if (pp instanceof AConstVarPrefixterm) {
            t = ((AConstVarPrefixterm)pp).getId();
            this.var = true;
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
        if (!this.gvars.contains(name)) {
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
        } else {
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
            try {
            this.prog.addDefFunctionSymbol(f);
            this.prog.setFunctionSignature(f, Symbol.MAINSIG);
            } catch (ProgramException e) {}
        } else if (f.getArity() != arity) {
            this.addParseError(t, "arity "+Integer.valueOf(f.getArity()).toString()+" expected for function symbol '"+name+"', not "+Integer.valueOf(arity).toString());
        }
        } else {
        this.addParseError(t, "defining function expected, not variable '"+name+"'");
        }

    }

    PTerm p = node.getLeft();
    Token t = null;
    boolean infix = false;
    if (p instanceof APrefixTerm) {
        PPrefixterm pp = ((APrefixTerm)p).getPrefixterm();
        if (pp instanceof AFunctAppPrefixterm) {
            t = ((AFunctAppPrefixterm)pp).getId();
        } else if (pp instanceof AConstVarPrefixterm) {
            t = ((AConstVarPrefixterm)pp).getId();
                this.var = true;
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
    if (!this.gvars.contains(name)) {
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
        } else {
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
        try {
            this.prog.addDefFunctionSymbol(f);
            this.prog.setFunctionSignature(f, Symbol.MAINSIG);
        } catch (ProgramException e) {}
        } else if (f.getArity() != arity) {
        this.addParseError(t, "arity "+Integer.valueOf(f.getArity()).toString()+" expected for function symbol '"+name+"', not "+Integer.valueOf(arity).toString());
        }
    } else {
        this.addParseError(t, "defining function expected, not variable '"+name+"'");
    }
    }

    public void checkandadd(Node node) {
        Token t;
        if (node instanceof APrefixIdiid) {
            t = ((APrefixIdiid)node).getId();
        } else {
            t = ((AInfixIdiid)node).getInfixid();
            this.addParseError(t, "infix identifier '"+this.chop(t)+"' not allowed for variables");
            return;
        }
    String name = this.chop(t);
    if (this.gvars.contains(name)) {
        this.addParseError(t, "redeclaration of variable '"+name+"'");
    } else {
        this.gvars.add(name);
    }
    }

}
