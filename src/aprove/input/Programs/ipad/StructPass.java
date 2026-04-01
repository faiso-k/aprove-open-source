package aprove.input.Programs.ipad;

import java.util.*;

import aprove.input.Generated.ipad.node.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

/** This pass just picks up all structures and creates the appropriate sorts.
 *  <p>
 *  Also, for each sort a corresponding equal_*
 *  function is defined with empty rules.
 *  And for every constructor a isa_*-function is added.
 * @author Christian Haselbach
 * @version $Id$
 */

class StructPass extends Pass {
    private TypeDefinition curTypeDef;
    private Sort cursort;


    @Override
    public void inAStruct(AStruct node) {
    TId id = node.getStructname();
    String name = this.chop(id);

    // checking that the reserved words "IPAD_ANY_TYPE" and "IPAD_ANY_SORT" are not used
    if (name.equals(Pass.ANY_TYPE_NAME) || name.equals(Pass.ANY_SORT_NAME)) {
        this.addParseError(id, "Sorry, but '"+name+"' is a reserved word and may not be used.");
    }

    this.curTypeDef = new TypeDefinition(TypeTools.getTypeCons(name,0));
    this.typeContext.addTypeDef(this.curTypeDef);
    Sort s = Sort.create(name);
    try {
        this.prog.addSort(s);
    }
    catch (ProgramException e) {
        this.addParseError(id, "redeclaration of symbol ''"+this.chop(id)+"''");
    }
    this.sorttoken.put(s.getName(), node.getStructname());
    // Add equals_s
    Vector<Sort> sorts = new Vector<Sort>();
    sorts.add(s);
    sorts.add(s);
    DefFunctionSymbol feq = DefFunctionSymbol.create(new String("equal_"+s.getName()), sorts, this.prog.getSort("bool"));
    s.setEqualOp(feq);
    feq.setTermination(true); // by construction
    try {
        this.prog.addPredefFunctionSymbol(feq);
        this.prog.setFunctionSignature(feq, Symbol.BOOLSIG);
        List<AlgebraTerm> inTy = new Vector<AlgebraTerm>();
        inTy.add(this.curTypeDef.getDefTerm());
        inTy.add(this.curTypeDef.getDefTerm());
        AlgebraTerm eqtyt = TypeTools.function(inTy,this.getDeclaredType("bool",null));
        this.typeContext.setSingleTypeOf(feq,TypeTools.autoQuan(eqtyt));
    }
    catch (ProgramException e) {
        this.addParseError(node.getStructname(), "cannot create equality test 'equal_"+s.getName()+"' for sort '"+s.getName());
    }
    this.cursort = s;
    }

    @Override
    public void inAConstr(AConstr node) {
    TId id = node.getCons();
    // Add isa_s
    Vector<Sort> sorts = new Vector<Sort>();
    sorts.add(this.cursort);
    DefFunctionSymbol fisa = DefFunctionSymbol.create(new String("isa_"+this.chop(id)), sorts, this.prog.getSort("bool"));
    fisa.setTermination(true); // by construction
    try {
        this.prog.addPredefFunctionSymbol(fisa);
        this.prog.setFunctionSignature(fisa, Symbol.BOOLSIG);
        List<AlgebraTerm> inTy = new Vector<AlgebraTerm>();
        inTy.add(this.curTypeDef.getDefTerm());
        AlgebraTerm eqtyt = TypeTools.function(inTy,this.getDeclaredType("bool",null));
        this.typeContext.setSingleTypeOf(fisa,TypeTools.autoQuan(eqtyt));
    }
    catch (ProgramException e) {
        this.addParseError(node.getCons(), "cannot create isa test 'isa_"+this.chop(id)+"' for sort '"+this.cursort.getName());
    }
    }

}
