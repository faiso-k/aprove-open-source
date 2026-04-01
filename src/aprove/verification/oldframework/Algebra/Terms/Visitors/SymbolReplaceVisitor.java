package aprove.verification.oldframework.Algebra.Terms.Visitors ;
import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
/**
 * The <code>SymbolReplaceVisitor</code>
 * replaces some symbols with others
 * @author Stephan Swiderski
 * @version $Id$
 */
public abstract class SymbolReplaceVisitor implements FineGrainedTermVisitor {

    @Override
    public Object caseVariable(AlgebraVariable v) {
       return AlgebraVariable.create(this.repOfVarSym(v.getVariableSymbol()));
    }

    @Override
    public Object caseDefFunctionApp(DefFunctionApp dfapp) {
    Iterator i = dfapp.getArguments().iterator();
    Vector<AlgebraTerm> nargs =  new Vector<AlgebraTerm>();
    while (i.hasNext()) {
        nargs.add((AlgebraTerm) ((AlgebraTerm)i.next()).apply(this));
    }
    return AlgebraFunctionApplication.create(
        this.repOfDefFuncSym(dfapp.getDefFunctionSymbol()),
        nargs);
    }

    @Override
    public Object caseConstructorApp(ConstructorApp capp) {
    Iterator i = capp.getArguments().iterator();
    Vector<AlgebraTerm> nargs = new Vector<AlgebraTerm>();
    while (i.hasNext()) {
        nargs.add((AlgebraTerm) ((AlgebraTerm)i.next()).apply(this));
    }
    return AlgebraFunctionApplication.create(
       this.repOfConsSym((ConstructorSymbol)capp.getFunctionSymbol()),
       nargs);
    }


    @Override
    public Object caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {
        return null;
    }

    /**
     * overload this method if replacing of <code>DefFunctionSymbols</code>
     * is needed
     */
    public SyntacticFunctionSymbol repOfDefFuncSym(DefFunctionSymbol f){
        return f;
    }


    /**
     * overload this method if replacing of <code>ConstructorSymbols</code>
     * is needed
     */
    public SyntacticFunctionSymbol repOfConsSym(ConstructorSymbol c){
        return c;
    }

    /**
     * overload this method if replacing of <code>VaribaleSymbols</code>
     * is needed
     */
    public VariableSymbol repOfVarSym(VariableSymbol v){
        return v;
    }
}
