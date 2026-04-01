package aprove.input.Programs.tes;

import java.util.*;

import aprove.input.Generated.tes.node.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Treewalker that implements the third pass of
 *  the AST conversion.
 *  <p>
 *  This pass picks up all rules for the defined
 *  functions. In a nutshell, this pass is a
 *  term parser.
 * @author Peter Schneider-Kamp, Stephan Falke
 * @version $Id$
 */

class Pass3 extends Pass {

    private DefFunctionSymbol curfun;
    private Stack<AlgebraTerm> terms = new Stack<AlgebraTerm>();
    private Vector<Rule> rules = new Vector<Rule>();
    private Hashtable vars = new Hashtable();
    private boolean lhs, condrule, equation, ac, c, a;

    @Override
    public void inASimpleRule(ASimpleRule node) {
    this.curfun = null;
    this.vars.clear();
        this.condrule = false;
        this.equation = false;
    }
    @Override
    public void outASimpleRule(ASimpleRule node) {
    AlgebraTerm left = this.terms.get(0);
        AlgebraTerm right = this.terms.get(1);
        if (this.equation) {
            TRSEquation e = TRSEquation.create(left, right);
            this.prog.addEquation(e);
        } else {
            if (left.isVariable()) {
                return;
            }
            Rule r = Rule.create(left, right);
            this.prog.addRule(this.curfun, r);
        }
    }
    @Override
    public void inAConditionalRule(AConditionalRule node) {
    this.curfun = null;
    this.rules.clear();
    GetVars gv = new GetVars();
    gv.setProgram(this.prog);
    gv.setVars(this.gvars);
    ((ASimple)((AConditional)node.getConditional()).getSimple()).getLeft().apply(gv);
    this.vars = new Hashtable(gv.getTermVars());
    this.condrule = true;
    this.equation = false;
    }
    @Override
    public void outAConditionalRule(AConditionalRule node) {
    AlgebraTerm left = this.terms.get(0);
    AlgebraTerm right = this.terms.get(1);
        if (!this.equation) {
            if (left.isVariable()) {
                return;
            }
        Rule r = Rule.create(new Vector<Rule>(this.rules), left, right);
        this.prog.addRule(this.curfun, r);
    }
    }

    @Override
    public void inASimple(ASimple node) {
    this.terms.clear();
    this.lhs = true;
    }
    @Override
    public void outASimple(ASimple node) {
    if (this.cond) {
        AlgebraTerm left = this.terms.get(0);
        AlgebraTerm right = this.terms.get(1);
        this.rules.add(Rule.create(left, right));
    }
    }

    @Override
    public void inAFunctAppPrefixterm(AFunctAppPrefixterm node) {
        if (this.gvars.contains(this.chop(node.getId()))) {
            // error
            return;
        }
    if (!this.cond && this.curfun == null) {
        this.curfun = this.prog.getDefFunctionSymbol(this.chop(node.getId()));
    }
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(this.chop(node.getId()));
    int size = ((ATermlist)node.getTermlist()).getTermcomma().size()+1;
    if (f.getArity() != size) {
        this.addParseError(node.getId(), "expected "+
                       Integer.valueOf(f.getArity()).toString()+
                       " parameters, not "+
                       Integer.valueOf(size).toString());
        // BEGIN "ugly hack"
        AlgebraTerm u = AlgebraVariable.create(VariableSymbol.create("undefined", this.poly));
        for (int i=0; i<f.getArity()-size; i++) {this.terms.add(u);}
        // END "ugly hack"
    }
    }
    @Override
    public void outAFunctAppPrefixterm(AFunctAppPrefixterm node) {
        if (this.gvars.contains(this.chop(node.getId()))) {
            // error
            return;
        }
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(this.chop(node.getId()));
    int size = f.getArity();
    Vector<AlgebraTerm> t = new Vector<AlgebraTerm>();
        for (int i=0; i<size; i++) {t.insertElementAt(this.terms.pop(),0);}
    this.terms.add(AlgebraFunctionApplication.create(f, t));
    }
    @Override
    public void caseTArrow(TArrow node) {
    this.lhs = false;
        if (this.chop(node).equals("==")) {
            this.equation = true;
            if (this.condrule) {
        if (!this.cond) {
                    this.addParseError(node, "equations must not have conditions");
        }
        else {
                    this.addParseError(node, "conditions must not be equations");
        }
            }
        }
    }
    @Override
    public void inAConstVarPrefixterm(AConstVarPrefixterm node) {
    String name = this.chop(node.getId());
    if (this.gvars.contains(name)) {
        VariableSymbol var = (VariableSymbol)this.vars.get(name);
            if (var == null) {
                // new variables may occur:
                //   l -> r                  : l
                //   s_i -> t_i | l -> r     : l, t_i
                //   l == r                  : l, r
                var = VariableSymbol.create(name, this.poly);
                this.vars.put(name, var);
        }
        this.terms.add(AlgebraVariable.create(var));
    } else {
            if (!this.cond && this.curfun == null) {
                this.curfun = this.prog.getDefFunctionSymbol(name);
            }
        SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
        if (f.getArity() != 0) {
        this.addParseError(node.getId(), "missing parameter list for function or constructor '"+name+"'");
        }
        this.terms.add(AlgebraFunctionApplication.create(this.prog.getFunctionSymbol(name)));
    }
    }

    @Override
    public void inAIninInfixterm(AIninInfixterm node) {
        String name = this.chop(node.getInfixid());
        //String name = escape(chop(node.getInfixid()));
    if (!this.cond && this.curfun == null) {
        this.curfun = this.prog.getDefFunctionSymbol(name);
    }
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
        int size = 0;
/*        ATermlist termlist = ((ATermlist)node.getTermlist());
        if (termlist != null) {
            size = termlist.getTermcomma().size()+1;
        }
    if (f.getArity() != size) {
        this.addParseError(node.getId(), "expected "+
                       Integer.valueOf(f.getArity()).toString()+
                       " parameters, not "+
                       Integer.valueOf(size).toString());
        // BEGIN "ugly hack"
        Term u = Variable.create(VariableSymbol.create("undefined", poly));
        for (int i=0; i<f.getArity()-size; i++) {terms.add(u);}
        // END "ugly hack"
    }*/
    }

    @Override
    public void outAIninInfixterm(AIninInfixterm node) {
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(this.chop(node.getInfixid()));
    //FunctionSymbol f = prog.getFunctionSymbol(escape(chop(node.getInfixid())));
    Vector<AlgebraTerm> t = new Vector<AlgebraTerm>();
        t.insertElementAt(this.terms.pop(),0);
    t.insertElementAt(this.terms.pop(),0);
    this.terms.add(AlgebraFunctionApplication.create(f, t));
    }

    @Override
    public void inAInpreInfixterm(AInpreInfixterm node) {
        String name = this.chop(node.getInfixid());
        //String name = escape(chop(node.getInfixid()));
    if (!this.cond && this.curfun == null) {
        this.curfun = this.prog.getDefFunctionSymbol(name);
    }
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
        int size = 0;
/*        ATermlist termlist = ((ATermlist)node.getTermlist());
        if (termlist != null) {
            size = termlist.getTermcomma().size()+1;
        }
    if (f.getArity() != size) {
        this.addParseError(node.getId(), "expected "+
                       Integer.valueOf(f.getArity()).toString()+
                       " parameters, not "+
                       Integer.valueOf(size).toString());
        // BEGIN "ugly hack"
        Term u = Variable.create(VariableSymbol.create("undefined", poly));
        for (int i=0; i<f.getArity()-size; i++) {terms.add(u);}
        // END "ugly hack"
    }*/
    }

    @Override
    public void outAInpreInfixterm(AInpreInfixterm node) {
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(this.chop(node.getInfixid()));
    //FunctionSymbol f = prog.getFunctionSymbol(escape(chop(node.getInfixid())));
    Vector<AlgebraTerm> t = new Vector<AlgebraTerm>();
        t.insertElementAt(this.terms.pop(),0);
    t.insertElementAt(this.terms.pop(),0);
    this.terms.add(AlgebraFunctionApplication.create(f, t));
    }

    @Override
    public void inAPreinInfixterm(APreinInfixterm node) {
        String name = this.chop(node.getInfixid());
        //String name = escape(chop(node.getInfixid()));
    if (!this.cond && this.curfun == null) {
        this.curfun = this.prog.getDefFunctionSymbol(name);
    }
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
        int size = 0;
/*        ATermlist termlist = ((ATermlist)node.getTermlist());
        if (termlist != null) {
            size = termlist.getTermcomma().size()+1;
        }
    if (f.getArity() != size) {
        this.addParseError(node.getId(), "expected "+
                       Integer.valueOf(f.getArity()).toString()+
                       " parameters, not "+
                       Integer.valueOf(size).toString());
        // BEGIN "ugly hack"
        Term u = Variable.create(VariableSymbol.create("undefined", poly));
        for (int i=0; i<f.getArity()-size; i++) {terms.add(u);}
        // END "ugly hack"
    }*/
    }

    @Override
    public void outAPreinInfixterm(APreinInfixterm node) {
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(this.chop(node.getInfixid()));
    //FunctionSymbol f = prog.getFunctionSymbol(escape(chop(node.getInfixid())));
    Vector<AlgebraTerm> t = new Vector<AlgebraTerm>();
        t.insertElementAt(this.terms.pop(),0);
    t.insertElementAt(this.terms.pop(),0);
    this.terms.add(AlgebraFunctionApplication.create(f, t));
    }

    @Override
    public void inAPrepreInfixterm(APrepreInfixterm node) {
        String name = this.chop(node.getInfixid());
        //String name = escape(chop(node.getInfixid()));
    if (!this.cond && this.curfun == null) {
        this.curfun = this.prog.getDefFunctionSymbol(name);
    }
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
        int size = 0;
/*        ATermlist termlist = ((ATermlist)node.getTermlist());
        if (termlist != null) {
            size = termlist.getTermcomma().size()+1;
        }
    if (f.getArity() != size) {
        this.addParseError(node.getId(), "expected "+
                       Integer.valueOf(f.getArity()).toString()+
                       " parameters, not "+
                       Integer.valueOf(size).toString());
        // BEGIN "ugly hack"
        Term u = Variable.create(VariableSymbol.create("undefined", poly));
        for (int i=0; i<f.getArity()-size; i++) {terms.add(u);}
        // END "ugly hack"
    }*/
    }

    @Override
    public void outAPrepreInfixterm(APrepreInfixterm node) {
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(this.chop(node.getInfixid()));
    //FunctionSymbol f = prog.getFunctionSymbol(escape(chop(node.getInfixid())));
    Vector<AlgebraTerm> t = new Vector<AlgebraTerm>();
        t.insertElementAt(this.terms.pop(),0);
    t.insertElementAt(this.terms.pop(),0);
    this.terms.add(AlgebraFunctionApplication.create(f, t));
    }

    @Override
    public void inAAcdecl(AAcdecl acs) {
        this.ac = true;
    }

    @Override
    public void outAAcdecl(AAcdecl acs) {
        this.ac = false;
    }

    @Override
    public void inACdecl(ACdecl acs) {
        this.c = true;
    }

    @Override
    public void outACdecl(ACdecl acs) {
        this.c = false;
    }

    @Override
    public void inAAdecl(AAdecl acs) {
        this.a = true;
    }

    @Override
    public void outAAdecl(AAdecl acs) {
        this.a = false;
    }

    @Override
    public void inAIdcomma(AIdcomma node) {
    if(this.ac || this.c || this.a) {
        this.checkandadd(node.getIdiid());
    }
    }

    @Override
    public void outAIdlist(AIdlist node) {
    if(this.ac || this.c || this.a) {
        this.checkandadd(node.getIdiid());
    }
    }

    public void checkandadd(Node node) {
        Token t;
        if (node instanceof APrefixIdiid) {
            t = ((APrefixIdiid)node).getId();
        } else {
            t = ((AInfixIdiid)node).getInfixid();
        }
    String name = this.chop(t);
    SyntacticFunctionSymbol fun = this.prog.getFunctionSymbol(name);
    if (fun != null) {
        if(this.ac) {
            this.prog.addEquations(EquationalTheory.createACTheory(fun, this.prog));
        }
        else if(this.c) {
            this.prog.addEquations(EquationalTheory.createCTheory(fun, this.prog));
        }
        else if(this.a) {
            this.prog.addEquations(EquationalTheory.createATheory(fun, this.prog));
        }
    }
    }

}
