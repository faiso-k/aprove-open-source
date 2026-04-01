package aprove.verification.oldframework.Typing;
import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * The <code>AbstractTypeVisitor</code> is an extension of a
 * {@link CoarseGrainedTermVisitor} for working with a local type assumption
 * (multiple type environment is not compatible with this visitor).
 * @author Stephan Swiderski
 * @version $Id$
 */
public abstract class AbstractTypeVisitor<T> implements CoarseGrainedTermVisitor<T> {
    protected FreshVarGenerator fvg;
    protected TypeContext tct;
    protected TypeAssumption ta;
    protected TypeAssumption locals; // allows this visitor to work with another type assumption

    public AbstractTypeVisitor(FreshVarGenerator fvg,TypeContext tct,TypeAssumption ta,TypeAssumption loc){
       this.ta = ta;
       this.fvg = fvg;
       this.tct = tct;
       this.locals = loc;
    }

    /**
     * returns a fresh type variable by using the current typecontext
     * @return fresh type variable
     */
    public AlgebraVariable getFreshVariable(){
        return TypeTools.getFreshTypeVariable(this.fvg);
    }

    /**
     * returns a fresh instance of the type of the given symbol
     * if the type of a the given symbol is not found, a new type
     * composed of a fresh type variable is created and stored in a local type assumption
     * @param sym the symbol
     * @return type term as fresh instance
     */
    public AlgebraTerm getFreshTypeTermOf(Symbol sym) throws TypingException {
        Set<Type> cts = this.ta.getTypesOf(sym);
    if (null == cts) { cts = this.tct.getTypesOfConstructor(sym);}
    if (null == cts) { cts = this.locals.getTypesOf(sym); }
    if (null == cts) {
        Type ct = new Type(new TypeQuantifier(),this.getFreshVariable());
        this.locals.setSingleTypeOf(sym,ct);
        return ct.getFreshInstance(this.fvg);
    }
    return TypeTools.toSingleType(cts).getFreshInstance(this.fvg);
    }

    /**
     * resets the local symbols
     * For a symbol which has no type declaration in the type context or type assumption
     * a new type (fresh type variable) is created and stored in a local type assumption
     * until this method is called.
     * This method should be called if the type visitor jump to another rule of a function.
     */
    public void resetLocals(){
        this.locals = new TypeAssumption.TypeAssumptionSkeleton();
    }

    /**
     * @return the type assumption of the local symbols
     */
    public TypeAssumption getLocalAssumption(){
        return this.locals;
    }

}

