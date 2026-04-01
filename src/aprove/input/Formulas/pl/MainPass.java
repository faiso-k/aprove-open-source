package aprove.input.Formulas.pl;

import java.util.*;

import aprove.input.Generated.pl.node.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** Treewalker that converts an abstract syntax tree to the internal formula representation.
 * @author RalfBehle, Stephan Falke, Christian Haselbach
 * @version $Id$
 */

class MainPass extends Pass {

    protected Stack<Formula> fs;
    protected Stack<AlgebraTerm> terms;

    protected Map<String,Sort> variableSortMapping;
    protected Stack<Sort> stackOfSorts;

    // Token bei dem die Sorte einer Variable (noch) nicht ermittelt werden konnte
    private Token unknownSortToken;

    @Override
    public void inStart(Start node) {
        this.fs                  = new Stack<Formula>();
        this.stackOfSorts         = new Stack<Sort>();
        this.variableSortMapping = new LinkedHashMap<String,Sort>();
    }

    @Override
    public void outStart(Start node) {
        this.formula = this.fs.pop();
    }

    @Override
    public void outAEquivFormula(AEquivFormula node) {
    Formula fright = (Formula)this.fs.pop();
    Formula fleft = (Formula)this.fs.pop();
    this.fs.push(Equivalence.create(fleft, fright));
    }

    @Override
    public void outAOrFormula(AOrFormula node) {
    Formula fright = (Formula)this.fs.pop();
    Formula fleft = (Formula)this.fs.pop();
    this.fs.push(Or.create(fleft, fright));
    }

    @Override
    public void outAAndFormula(AAndFormula node) {
    Formula fright = (Formula)this.fs.pop();
    Formula fleft = (Formula)this.fs.pop();
    this.fs.push(And.create(fleft, fright));
    }

    @Override
    public void outAImplicationFormula(AImplicationFormula node) {
    Formula fright = (Formula)this.fs.pop();
    Formula fleft = (Formula)this.fs.pop();
    this.fs.push(Implication.create(fleft, fright));
    }

    @Override
    public void outANegSformula(ANegSformula node) {
    Formula f = (Formula)this.fs.pop();
    this.fs.push(Not.create(f));
    }

    @Override
    public void caseATtSformula(ATtSformula node) {
    this.fs.push(FormulaTruthValue.create(true));
    }

    @Override
    public void caseAFfSformula(AFfSformula node) {
    this.fs.push(FormulaTruthValue.create(false));
    }

    @Override
    public void caseAAtomSformula(AAtomSformula node) {
        this.terms = new Stack<AlgebraTerm>();
        node.getLeft().apply(this);
        AlgebraTerm left = null;
        if (!this.terms.isEmpty()) {
            left = (AlgebraTerm) this.terms.pop();
        }
        this.terms = new Stack<AlgebraTerm>();
        if(left!=null){
            this.stackOfSorts.push(left.getSort());
        }
        node.getRight().apply(this);
        if (!this.stackOfSorts.isEmpty()){
            this.stackOfSorts.pop();
        }
        AlgebraTerm right = null;
        if (!this.terms.isEmpty()){
            right = (AlgebraTerm) this.terms.pop();
        }
        // falls die Sorte der linken Seite noch unbekannt ist, weil dort eine Variable steht,
        // als Sorte der linken Seite die Sorte der rechten Seite setzen,
        // sofern der rechte Term erfolgreicht geparst wurde und dessen Sorte bekannt ist
        if (right != null && left != null && left.getSort() == null && left.isVariable()){
            Sort rightSort = right.getSort();
            if (rightSort == null){
                this.addParseError(this.unknownSortToken, "Could not determine sort of one of the variables '"+left.toString()+"' and '"+right.toString()+"' please specify one.");
            }
            else{
                this.variableSortMapping.put(left.getSymbol().getName(),rightSort);
                left.getSymbol().setSort(rightSort);
            }
        }

        this.fs.push(Equation.create(left, right));
    }


    @Override
    public void inAVarNterm(AVarNterm node) {
        Token id = node.getId();
        String name = this.chop(id);
        Symbol sym = this.prog.getSymbol(name);
        if (sym != null) {
            this.addParseError(id, "Symbol name already used");
        } else {

            Sort sort = this.variableSortMapping.get(name);
            if(sort == null) {
                // falls bekannt, der Variable die Sorte zuweisen, sonst NULL zuweisen
                if (!this.stackOfSorts.isEmpty()) {
                    sort = this.stackOfSorts.peek();
                } else {
                    this.unknownSortToken = id;
                }
                this.variableSortMapping.put(name,sort);
            }else{
                try {
                    if(!this.stackOfSorts.peek().equals(sort)) {
                        this.addParseError(id, "Variable has the wrong sort '"+name+"'");
                        return;
                    }
                }catch(EmptyStackException e) {}
            }
            this.terms.add(AlgebraVariable.create(VariableSymbol.create(name, sort)));
        }
    }

    @Override
    public void inAConstNterm(AConstNterm node) {
    Token id = node.getPrefixId();
    String name = this.chop(id);
    Symbol sym = this.prog.getSymbol(name);
    if (((SyntacticFunctionSymbol)sym).getArity() != 0) {
        this.addParseError(id, "missing parameter list for function or constructor '"+name+"'");
        return;
    }
    this.terms.add(AlgebraFunctionApplication.create((SyntacticFunctionSymbol)sym));
    }

    @Override
    public void caseAFunctAppNterm(AFunctAppNterm node) {
    Token id = node.getPrefixId();
    int size = ((ATermlist)node.getTermlist()).getTermcomma().size()+1;
    String name = this.chop(id);
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
        if (f == null) {
            f = this.prog.getPredefFunctionSymbol(name);
            if (f != null) {
                try {
                    this.prog.activatePredefFunctionSymbol(name);
                } catch (ProgramException e) {
            this.addParseError(id, "'"+name+"' already declared in program");
            return;
                }
            }
        }
        if (f == null) {
        this.addParseError(id, "undeclared function or constructor '"+name+"'");
        return;
    }
    else {
        if (f.getArity() != size) {
        this.addParseError(id, "expected "+Integer.valueOf(f.getArity()).toString()+" parameters, not "+Integer.valueOf(size).toString());
        return;
        }
    }

    Object[] object = ((ATermlist)node.getTermlist()).getTermcomma().toArray();
    int argument;

    for(argument=0; argument < object.length; argument++) {
        this.stackOfSorts.push(f.getArgSort(argument));
        ((ATermcomma)object[argument]).apply(this);
        this.stackOfSorts.pop();
    }

    this.stackOfSorts.push(f.getArgSort(argument));
    ((ATermlist)node.getTermlist()).getTerm().apply(this);
    this.stackOfSorts.pop();

    size = f.getArity();
    Vector<AlgebraTerm> t = new Vector<AlgebraTerm>();
    for (int i=0; i<size; i++) {t.insertElementAt((AlgebraTerm)this.terms.pop(), 0);}
    this.terms.add(AlgebraFunctionApplication.create(f, t));
    }

    @Override
    public void caseAInfixTerm(AInfixTerm node) {
    Token id = node.getInfixId();
    String name = this.chop(id);
    SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
        if (f == null) {
            f = this.prog.getPredefFunctionSymbol(name);
            if (f != null) {
                try {
                    this.prog.activatePredefFunctionSymbol(name);
                } catch (ProgramException e) {
                    this.addParseError(id,"'"+name+"' already declared in program");
            return;
                }
            }
        }
        if (f == null) {
            this.addParseError(id,"undeclared function or constructor '"+name+"'");
        return;
    }
    List<AlgebraTerm> ts = new Vector<AlgebraTerm>();
    this.stackOfSorts.push(f.getArgSort(0));
    node.getLeft().apply(this);
    this.stackOfSorts.pop();
    ts.add(this.terms.pop());
    this.stackOfSorts.push(f.getArgSort(1));
    node.getRight().apply(this);
    this.stackOfSorts.pop();
    ts.add(this.terms.pop());
    this.terms.add(AlgebraFunctionApplication.create((SyntacticFunctionSymbol)f, ts));
    }



    @Override
    public void caseATypedef(ATypedef node) {

        node.getType().apply(this);

        Token variable = node.getId();
        VariableSymbol variableSymbol = VariableSymbol.create(this.chop(variable));

        if(this.prog.getSymbol(this.chop(variable)) != null) {
            this.addParseError(variable,"Symbol already used");
            return;
        }

        this.variableSortMapping.put(variableSymbol.getName(), this.stackOfSorts.pop());
    }

    @Override
    public void inAType(AType node) {

        Token colon = node.getColon();
        if( !this.chop(colon).equals(":")) {
            this.addParseError(colon,"Expected \":\" ");
        }

        Token sortToken = node.getType();
        Sort sort = this.prog.getSort(this.chop(sortToken));
        if(sort == null) {
            this.addParseError(sortToken,"unknown sort");
            return;
        }

        this.stackOfSorts.push(sort);
    }

}
