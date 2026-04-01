package aprove.verification.oldframework.Typing;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * A <code>TypeContext</code> contains the haskell-like data structurs for one Programm
 * @author Stephan Swiderski
 * @version $Id$
 */
public class TypeContext implements java.io.Serializable{
    protected TypeAssumption.TypeAssumptionSkeleton    curTa;
    protected Map<Symbol,TypeDefinition> typeDefMap;


    /**
     * construct an empty type context
     */
    public TypeContext(){
        this.curTa = new TypeAssumption.TypeAssumptionSkeleton();
        this.typeDefMap = new LinkedHashMap<Symbol,TypeDefinition>();
    }

    /**
     * get the set of types of the given constructor symbol by using the type definitions
     * <p> used by type assumptions of this type context
     * @param sym the constructor symbol
     * @return the set of types
     */
    protected Set<Type> getTypesOfConstructor(Symbol sym){
        for(Map.Entry<Symbol,TypeDefinition> entry : this.typeDefMap.entrySet() ) {
            TypeDefinition td = entry.getValue();
            Set<Type> types = td.getTypesOf(sym);
            if (null != types) { return types; }
        }
        return null;
    }

    /**
     * get the type cons with the given name
     * @param name
     * @return the type cons with the name
     */
    public ConstructorSymbol getTypeCons(String name){
        TypeDefinition td = this.getTypeDef(name);
    if (td != null) { return td.getTypeCons(); }
    return null;
    }

    /**
     * get the type definition of the type constructor with the given name
     * @param name
     * @return the type definition (null if name is unknown)
     */
    public TypeDefinition getTypeDef(String name){
        for(Map.Entry<Symbol,TypeDefinition> entry : this.typeDefMap.entrySet() ) {
            TypeDefinition td = entry.getValue();
            if (name.equals(td.getTypeCons().getName())) {
                return td;
            }
        }
        return null;
    }

    /**
     * Gets the set of types of a symbol by using the current
     * type assumption and type definitions of this type context.
     * @param sym the symbol
     * @return a set of types (null if symbol is unknown)
     */
    public Set<Type> getTypesOf(Symbol sym){
        Set<Type> ct = this.getTypesOfConstructor(sym);
    if (null == ct) { ct = this.curTa.getTypesOf(sym); }
    return ct;
    }

    /**
     * Sets the set of types of a symbol
     * @param sym the symbol
     * @param types set of types
     */
    public void setTypesOf(Symbol sym,Set<Type> types){
        this.curTa.setTypesOf(sym,types);
    }

    /**
     * returns the assumed type of a symbol.
     * @param sym
     * @return a the type for the function, constructor or variable symbole sym
     */
    public Type getSingleTypeOf(Symbol sym) {
        try {
            return TypeTools.toSingleType(this.getTypesOf(sym));
        } catch (TypingException e) {
            throw new RuntimeException(e.getMessage());
        }
    }

    /**
     * sets the single type of a symbol.
     * @param sym the symbol
     * @param type the type
     */
    public void setSingleTypeOf(Symbol sym,Type type) {

        if( "y".equals(sym.getName())) {
            throw new RuntimeException("Argh!!!!!!!!");
        }

        this.curTa.setSingleTypeOf(sym,type);
    }

    /**
     * removes the type of a symbol
     * @param sym the symbol
     */
    public void removeTypesOf(Symbol sym) {
        this.curTa.removeTypesOf(sym);
    }

    /**
     * Returns the type definition of the given type constructor symbol.
     * @param sym the type constructor symbol.
     * @return the type definition (null if symbol unknown)
     */
    public TypeDefinition getTypeDefOf(ConstructorSymbol sym){
        return (TypeDefinition) this.typeDefMap.get(sym);
    }

    /**
     * Returns the type definition of the root type constructor symbol
     * of the given typeterm
     * @param typeTerm the type constructor symbol.
     * @return the type definition (null if symbol unknown)
     */
    public TypeDefinition getTypeDefOfRootTypeCons(AlgebraTerm t){
        AlgebraFunctionApplication typeTerm =(AlgebraFunctionApplication) t;
        return (TypeDefinition) this.typeDefMap.get((ConstructorSymbol)typeTerm.getSymbol());
    }

     /**
     * Returns the set of type definitions
     * @return the set of type definitions
     */
    public Set<TypeDefinition> getTypeDefs(){
        return new LinkedHashSet<TypeDefinition>(this.typeDefMap.values());
    }

    /**
     * Adds a type definition to this type context.
     * This method will overwrite an exitent type definition, if that
     * have the same type constructor symbol.
     * @param td the type definition
     */
    public void addTypeDef(TypeDefinition td){
        this.typeDefMap.put(td.getTypeCons(),td);
    }

    /**
     * removes a type definition form this type context, adresses by the
     * type constructor symbol.
     * @param sym the type constructor symbol
     */
    public void removeTypeDefOf(ConstructorSymbol sym){
        this.typeDefMap.remove(sym);
    }

    /**
     * Checks the type of the term t
     * @param t term to check the type
     * @return the type term of t (null if t is not type correct)
     */
    public AlgebraTerm typeCheck(FreshVarGenerator ftvg, AlgebraTerm t){
        TypeCheckerVisitor tcv = new TypeCheckerVisitor(ftvg,this,new TypeAssumption.TypeAssumptionSkeleton());
        return t.apply(tcv);
    }

    public AlgebraTerm typeCheck(FreshVarGenerator freshVarGenerator, AlgebraTerm term, TypeAssumption typeAssumption) {
        TypeCheckerVisitor tcv = new TypeCheckerVisitor(freshVarGenerator,this, typeAssumption);
        return term.apply(tcv);
    }

    /**
     * shallow copy make no sense so it will do a deepcopy
     */
    public TypeContext shallowcopy(){
       return this.deepcopy();
    }

    /**
     * @return a deep copy of this object
     */
    public TypeContext deepcopy(){
        TypeContext ntct = new TypeContext();
        ntct.curTa = this.curTa.deepcopy();

        for(Map.Entry<Symbol,TypeDefinition> entry : this.typeDefMap.entrySet() ) {
            TypeDefinition td = entry.getValue();
            ntct.addTypeDef((TypeDefinition) td.deepcopy());
        }
        return ntct;

    }

    /*
     * @return a string representation of this object
     */
    @Override
    public String toString(){
        String out = new String();
        for(Map.Entry<Symbol,TypeDefinition> entry : this.typeDefMap.entrySet() ) {
            TypeDefinition td = entry.getValue();
            out = out + td.toString() + "\n";
        }
        return out + this.curTa.toString();
    }


}
