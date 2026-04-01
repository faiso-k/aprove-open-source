package aprove.input.Programs.tes;

import java.util.*;

import aprove.input.Generated.tes.node.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Treewalker that implements the second pass of
 *  the AST conversion.
 *  <p>
 *  This pass picks up all constructors.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

class Pass2 extends Pass {

    @Override
    public void inAFunctAppPrefixterm(AFunctAppPrefixterm node) {
    Token t = node.getId();
    String name = this.chop(t);
    if (this.gvars.contains(name)) {
        this.addParseError(t, "function symbol expected, not variable '"+name+"'");
    } else if (this.prog.getDefFunctionSymbol(name) == null) {
        ConstructorSymbol c;
        int arity = ((ATermlist)node.getTermlist()).getTermcomma().size()+1;
        c = this.prog.getConstructorSymbol(name);
        if (c == null) {
        c = ConstructorSymbol.create(name, new Vector<Sort>(), this.poly);
        for (int i=0; i<arity; i++) {
            c.addArgSort(this.poly);
        }
        this.poly.addConstructorSymbol(c);
        try {this.prog.addConstructorSymbol(c);} catch (ProgramException e) {}
        } else if (c.getArity() != arity) {
        this.addParseError(t, "arity "+Integer.valueOf(c.getArity()).toString()+" expected for constructor symbol '"+name+"', not "+Integer.valueOf(arity).toString());
        }
    }
    }

    @Override
    public void inAConstVarPrefixterm(AConstVarPrefixterm node) {
    String name = this.chop(node.getId());
    if (!this.gvars.contains(name)) {
        if (this.prog.getDefFunctionSymbol(name) == null) {
        ConstructorSymbol c = this.prog.getConstructorSymbol(name);
        if (c == null) {
            c = ConstructorSymbol.create(name, new Vector<Sort>(), this.poly);
            this.poly.addConstructorSymbol(c);
            try {this.prog.addConstructorSymbol(c);} catch (ProgramException e) {}
        } else if (c.getArity() != 0) {
            this.addParseError(node.getId(), "arity "+Integer.valueOf(c.getArity()).toString()+" expected for constructor symbol '"+name+"', not 0");
        }
        }
    }

    }

    @Override
    public void inAIninInfixterm(AIninInfixterm node) {
    Token t = node.getInfixid();
        String name = this.chop(t);
    //String name = escape(chop(t));
    if (this.gvars.contains(name)) {
        this.addParseError(t, "function symbol expected, not variable '"+name+"'");
    } else if (this.prog.getDefFunctionSymbol(name) == null) {
        ConstructorSymbol c;
        int arity = 2;
        c = this.prog.getConstructorSymbol(name);
        if (c == null) {
        c = ConstructorSymbol.create(name, new Vector<Sort>(), this.poly);
        for (int i=0; i<arity; i++) {
            c.addArgSort(this.poly);
        }
        this.poly.addConstructorSymbol(c);
        c.setFixity(SyntacticFunctionSymbol.INFIX);
        try {this.prog.addConstructorSymbol(c);} catch (ProgramException e) {}
        } else if (c.getArity() != arity) {
        this.addParseError(t, "arity "+Integer.valueOf(c.getArity()).toString()+" expected for constructor symbol '"+name+"', not "+Integer.valueOf(arity).toString());
        }
    }
    }

       @Override
    public void inAInpreInfixterm(AInpreInfixterm node) {
    Token t = node.getInfixid();
        String name = this.chop(t);
    //String name = escape(chop(t));
    if (this.gvars.contains(name)) {
        this.addParseError(t, "function symbol expected, not variable '"+name+"'");
    } else if (this.prog.getDefFunctionSymbol(name) == null) {
        ConstructorSymbol c;
        int arity = 2;
        c = this.prog.getConstructorSymbol(name);
        if (c == null) {
        c = ConstructorSymbol.create(name, new Vector<Sort>(), this.poly);
        for (int i=0; i<arity; i++) {
            c.addArgSort(this.poly);
        }
        this.poly.addConstructorSymbol(c);
        c.setFixity(SyntacticFunctionSymbol.INFIX);
        try {this.prog.addConstructorSymbol(c);} catch (ProgramException e) {}
        } else if (c.getArity() != arity) {
        this.addParseError(t, "arity "+Integer.valueOf(c.getArity()).toString()+" expected for constructor symbol '"+name+"', not "+Integer.valueOf(arity).toString());
        }
    }
    }

    @Override
    public void inAPreinInfixterm(APreinInfixterm node) {
    Token t = node.getInfixid();
    String name = this.chop(t);
    //String name = escape(chop(t));
    if (this.gvars.contains(name)) {
        this.addParseError(t, "function symbol expected, not variable '"+name+"'");
    } else if (this.prog.getDefFunctionSymbol(name) == null) {
        ConstructorSymbol c;
        int arity = 2;
        c = this.prog.getConstructorSymbol(name);
        if (c == null) {
        c = ConstructorSymbol.create(name, new Vector<Sort>(), this.poly);
        for (int i=0; i<arity; i++) {
            c.addArgSort(this.poly);
        }
        this.poly.addConstructorSymbol(c);
        c.setFixity(SyntacticFunctionSymbol.INFIX);
        try {this.prog.addConstructorSymbol(c);} catch (ProgramException e) {}
        } else if (c.getArity() != arity) {
        this.addParseError(t, "arity "+Integer.valueOf(c.getArity()).toString()+" expected for constructor symbol '"+name+"', not "+Integer.valueOf(arity).toString());
        }
    }
    }

    @Override
    public void inAPrepreInfixterm(APrepreInfixterm node) {
    Token t = node.getInfixid();
    String name = this.chop(t);
    //String name = escape(chop(t));
    if (this.gvars.contains(name)) {
        this.addParseError(t, "function symbol expected, not variable '"+name+"'");
    } else if (this.prog.getDefFunctionSymbol(name) == null) {
        ConstructorSymbol c;
        int arity = 2;
        c = this.prog.getConstructorSymbol(name);
        if (c == null) {
        c = ConstructorSymbol.create(name, new Vector<Sort>(), this.poly);
        for (int i=0; i<arity; i++) {
            c.addArgSort(this.poly);
        }
        this.poly.addConstructorSymbol(c);
        c.setFixity(SyntacticFunctionSymbol.INFIX);
        try {this.prog.addConstructorSymbol(c);} catch (ProgramException e) {}
        } else if (c.getArity() != arity) {
        this.addParseError(t, "arity "+Integer.valueOf(c.getArity()).toString()+" expected for constructor symbol '"+name+"', not "+Integer.valueOf(arity).toString());
        }
    }
    }

}
