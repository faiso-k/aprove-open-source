package aprove.input.Programs.fp;

import java.util.*;

import aprove.input.Generated.fp.node.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

/** Treewalker that implements the first pass of
 *  the AST conversion.
 *  <p>
 *  This pass basically just picks up all structures
 *  and creates the appropriate sorts.
 *  <p>
 *  Also, for each sort a corresponding isa_*
 *  function is defined as well as an equal_*
 *  with empty rules.
 * @author Peter Schneider-Kamp, Christian Haselbach
 * @version $Id$
 */

class Pass1 extends Pass {
    private TypeDefinition curTypeDef;
    private AlgebraTerm BoolCon;

    private Sort curSort = null;

    @Override
    public void inStart(Start node) {
    this.curTypeDef = null;
    }

    @Override
    public void inAStruct(AStruct node) {
    String name = this.chop(node.getStructname());
    this.curTypeDef = new TypeDefinition(TypeTools.getTypeCons(name,0));
    this.typeContext.addTypeDef(this.curTypeDef);
    this.usedNames.add(name);
    Sort s = Sort.create(name);
    try {
        this.prog.addSort(s);
    }
    catch (ProgramException e) {
        this.redeclaration(node.getStructname());
    }
    this.sorttoken.put(s.getName(), node.getStructname());
    this.curSort = s;
    AlgebraTerm t = AlgebraVariable.create(VariableSymbol.create("t", s)); // seems useless
    AlgebraTerm f = AlgebraVariable.create(VariableSymbol.create("f", s)); // seems useless
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    DefFunctionSymbol feq = DefFunctionSymbol.create(new String("equal_"+s.getName()), new Vector<Sort>(), this.prog.getSort("bool"));
    s.setEqualOp(feq);
    feq.setTermination(true); // by construction
    feq.addArgSort(s);
    feq.addArgSort(s);
    try {
        this.prog.addPredefFunctionSymbol(feq);
        feq.setSignatureClass(Symbol.BOOLSIG);
        List<AlgebraTerm> inTy = new Vector<AlgebraTerm>();
        inTy.add(this.curTypeDef.getDefTerm());
        inTy.add(this.curTypeDef.getDefTerm());
        AlgebraTerm eqtyt = TypeTools.function(inTy,this.getDeclaredType("bool",null));
        this.typeContext.setSingleTypeOf(feq,TypeTools.autoQuan(eqtyt));
    }
    catch (ProgramException e) {
        this.addParseError(node.getStructname(), "cannot create equality test 'equal_"+s.getName()+"' for sort '"+s.getName());
    }
    }

    @Override
    public void outAConstr(AConstr node) {
    String retSortName = this.chop(node.getReturn());
    Node cons = node.getCons();
    if (cons instanceof ANoappEid) {
        this.makeIsaCons(((ANoappEid)cons).getNoappid(), retSortName);
    }
    else {
        this.makeIsaCons(((AAppEid)cons).getId(), retSortName);
    }
    }

    @Override
    public void outAInfixconstr(AInfixconstr node) {
    String retSortName = this.chop(node.getReturn());
    this.makeIsaCons(node.getCons(), retSortName);
    }

    public void makeIsaCons(Token constructorToken, String retSortName) {
    // Add isa_cons
    Vector<Sort> sorts = new Vector<Sort>();
    sorts.add(this.curSort);
    String isaname = "isa_"+this.chop(constructorToken);
    this.usedNames.add(isaname);
    DefFunctionSymbol fisa = DefFunctionSymbol.create(isaname, sorts, this.prog.getSort("bool"));
    fisa.setTermination(true); // by construction
    try {
        this.prog.addPredefFunctionSymbol(fisa);
        fisa.setSignatureClass(Symbol.BOOLSIG);
        List<AlgebraTerm> inTy = new Vector<AlgebraTerm>();
        inTy.add(this.curTypeDef.getDefTerm());
        AlgebraTerm eqtyt = TypeTools.function(inTy,this.getDeclaredType("bool",null));
        this.typeContext.setSingleTypeOf(fisa,TypeTools.autoQuan(eqtyt));
    }
    catch (ProgramException e) {
        this.addParseError(constructorToken, "cannot create isa test '"+isaname+"' for sort '"+this.curSort.getName());
    }
    }
}
