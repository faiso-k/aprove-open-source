package aprove.verification.oldframework.Typing;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;
/**
 * A <code>TypeDefinition</code> contain a haskell-like data structur.
 * <p>
 * Haskell interpretation: <code>data typCons (a,b,c) = cons1 | ... | cons2 </code> <p>
 * Important: <p>
 * All constructor types in a type definition
 * share the same quantifier <code>quan</code>.
 * Term <code>defTerm</code> contains the same
 * varibales as the quantifier <code>quan</code>.
 *
 * @author Stephan Swiderski
 * @version $Id$
 */
public class TypeDefinition extends TypeAssumption.TypeAssumptionSkeleton {

    /* quantified variables */
    protected TypeQuantifier quan;

    /* this definied type */
    private AlgebraFunctionApplication defTerm;

    /* witness terms are only possible if the {@link TypeContext} of this type definition
     * is monomorphic
     */
    private AlgebraTerm witnessTerm;

    /* constructors */

    public  TypeDefinition(AlgebraFunctionApplication defTerm, TypeQuantifier quan, AlgebraTerm witnessTerm, Map<Symbol,Set<Type>> typeMap) {
        this.defTerm     = defTerm;
        this.quan         = quan;
        this.witnessTerm = witnessTerm;
        this.typeMap     = typeMap;
    }

    /**
     * creates a new type definition of this form: <code>data DT a1 .. an = ()</code>
     * (<code>ai</code> are Variables)
     * <p> i.e. there are no constructors in this new type definitions
     * @param defTerm type constructor term: <code>DT a1 ... an</code>
     */
    public TypeDefinition(AlgebraTerm defTerm) {
        super();
        this.quan = new TypeQuantifier();
    this.setDefTerm(defTerm);
    this.witnessTerm = null;
    }

    /**
     * creates a new type definition of this form:  <code>data DT = ()</code>
     * <p> i.e. there are no constructors in this new type definitions
     * @param sym type constructor (0-arity)
     */
    public TypeDefinition(ConstructorSymbol sym) {
        super();
        this.quan = new TypeQuantifier();
    this.setDefTerm(AlgebraFunctionApplication.create(sym));
    this.witnessTerm = null;
    }

    /**
     * creates a new type definition for one n-arity constructor
     * <p> i.e. <code> data DT a1 .. an = c(a1,...,an) </code>
     * @param fvg for new vars (namely <code>ai</code>)
     * @param tconSym the type constructor (<code>DT</code>)
     * @param conSym the constructor (<code>c</code>)
     */
    public TypeDefinition(FreshVarGenerator fvg,ConstructorSymbol tconSym,ConstructorSymbol conSym) {
        super();
        this.quan = new TypeQuantifier();
    List<AlgebraTerm> lt = new Vector<AlgebraTerm>();
    int arity = conSym.getArity();
    for(int i = 0; i < arity; i++){
       AlgebraVariable v = TypeTools.getFreshTypeVariable(fvg);
           lt.add(v);
       this.quan.add(v);
    }
        this.defTerm = AlgebraFunctionApplication.create(tconSym,lt);

        Set<Type> sot = new HashSet<Type>();
    sot.add(new Type(this.quan,TypeTools.function(lt,this.defTerm)));
        this.setTypesOf((Symbol)conSym,sot);
    this.witnessTerm = null;
    }

    /**
     * renames all quantified variables in fresh ones
     * of given {@link TypeContext}.
     * @param fvg for new vars
     * @return substitution for some type terms in context of this quantifier
     */
    protected AlgebraSubstitution refreshVars(FreshVarGenerator fvg){
        AlgebraSubstitution ren = this.quan.refreshVars(fvg);
    this.defTerm = (AlgebraFunctionApplication) this.defTerm.apply(ren);
    return ren;
    }

    /**
     * Gets the type-constructorsymbol of this defined type
     */
    public ConstructorSymbol getTypeCons(){
         return (ConstructorSymbol) this.defTerm.getSymbol();
    }

    /**
     * Gets the Term TypeCons(a1, ,aN) of this
     * type definition data TypeCons(a1, ,aN) = co1|  | coM  .
     */
    public AlgebraTerm getDefTerm(){
         return this.defTerm;
    }

    /**
     * Sets the Term TypeCons(a1, ,aN) of this
     * type definition data TypeCons(a1, ,aN) = co1|  | coM  .
     */
    protected void setDefTerm(AlgebraTerm defTerm){
         this.defTerm = (AlgebraFunctionApplication) defTerm;
     this.quan.clear();
     this.quan.addAll(defTerm.getVars());
     if (this.defTerm.getFunctionSymbol().getArity() != this.quan.size()) {
             throw new RuntimeException("Repetition of variables in deftype term: " + defTerm.toString());
     }
    }

    /**
     * The types in a type definition share the same quantifier
     * but sometimes the quantifiers of types of constructors in this definition
     * are replaced. That Method will
     */
    protected void correctQuantifiers(){
    Iterator it = this.typeMap.entrySet().iterator();
        while (it.hasNext()){
            Map.Entry entry = (Map.Entry) it.next();
            Iterator jt = ((Set<Type>) entry.getValue()).iterator();
        while (jt.hasNext()){
           ((Type) jt.next()).typeQuantifier = this.quan;
        }
        }
    }


    /**
     * Adds a type declaration (cons:t1/.../tn) to this type definition.
     * @param sym symbol (should be a constructor symbol)
     * @param taus dedicated set of type
     */
    @Override
    public void setTypesOf(Symbol sym,Set<Type> taus){
         Set<Type> ntaus = new HashSet<Type>();
         Iterator jt = taus.iterator();
     while (jt.hasNext()){
         AlgebraTerm matrix = ((Type) jt.next()).getTypeMatrix();
             ntaus.add(new Type(this.quan,matrix));
         }
     super.setTypesOf(sym,ntaus);
    }


    /**
     * add constructors declared in a type assumption to this type definition
     * A symbol, defined in the type assumption ta and this type definition,
     * will get the type which is declared in the type assumption ta.
     * The type assumption ta will be destroyed.
     * @param ta typeassumption
     */
    public void addConstructors(TypeAssumption.TypeAssumptionSkeleton ta){
        this.typeMap.putAll(ta.typeMap);
    this.correctQuantifiers();
    }

    /**
     * Construct a deep copy of this type definition in the same {@link TypeContext}.
     * @return a new type assumption
     */
    @Override
    public TypeAssumption.TypeAssumptionSkeleton deepcopy(){
        TypeDefinition td = new TypeDefinition(this.defTerm.deepcopy());
    Iterator it = this.typeMap.entrySet().iterator();
        while (it.hasNext()){
            Map.Entry entry = (Map.Entry) it.next();
        Symbol csym = (Symbol)entry.getKey();
            Set<Type> sot = new HashSet<Type>();
            Iterator jt = ((Set<Type>) entry.getValue()).iterator();
        while (jt.hasNext()){
           sot.add(new Type(td.quan,((Type) jt.next()).getTypeMatrix().deepcopy()));
        }
            td.setTypesOf(csym,sot);
        }
    td.setWitnessTerm(this.getWitnessTerm());
    return td;
    }

    /**
     * sets the witness term of this data structure.
     * @param witnessTerm the witness term
     */
    public void setWitnessTerm(AlgebraTerm witnessTerm){
        this.witnessTerm = witnessTerm;
    }

    /**
     * returns the witness term of this data structure.
     * @return the witness term
     */
    public AlgebraTerm getWitnessTerm(){
        return this.witnessTerm;
    }

    /*
     * @return a string representation of this object
     */
    @Override
    public String toString(){
        String was = " = ";
        String pipe = "| ";
        String line = "/";
        String out = "data ";
        out = out + this.quan.toString() + this.defTerm.toString();
        Iterator it = this.typeMap.entrySet().iterator();
        while (it.hasNext()){
            Map.Entry entry = (Map.Entry) it.next();
        SyntacticFunctionSymbol csym = (SyntacticFunctionSymbol)entry.getKey();
            Iterator jt = ((Set<Type>) entry.getValue()).iterator();
            String cwas = "";
            String cto = "";
        while (jt.hasNext()){
          Type ct = (Type) jt.next();
          List<AlgebraTerm> lt = TypeTools.getArguments(ct.getTypeMatrix());
          String pars = " ";
              Iterator kt = lt.iterator();
              while (kt.hasNext()){
                  pars = pars + ((AlgebraTerm)kt.next()).toString() + " ";
              }
          cto = cto + cwas + csym.getName() + pars;
          cwas = line;
        }
        out = out + was + cto;
        was = pipe;
        }
    if (this.witnessTerm != null) { return out +" -- "+ this.witnessTerm.toString(); }
        return out;
    }

    public TypeQuantifier getTypeQuantifier() {
        return this.quan;
    }

    public String toHTML() {
        StringBuffer stringBuffer = new StringBuffer();

        return stringBuffer.toString();
    }

    @Override
    public boolean equals(Object that) {

        if(that instanceof TypeDefinition) {

            TypeDefinition thatTypeDefinition = (TypeDefinition)that;

            boolean t = this.defTerm.equals(thatTypeDefinition.defTerm) &&  this.quan.equals(thatTypeDefinition.quan);
            t = t && this.witnessTerm.equals(thatTypeDefinition.witnessTerm);
            t = t && this.typeMap.equals(thatTypeDefinition.typeMap);

            System.out.println(this.typeMap);
            System.out.println(thatTypeDefinition.typeMap);

            return t;
        }

        return false;
    }

    @Override
    public int hashCode() {
        return this.defTerm.toString().hashCode();
    }
}

