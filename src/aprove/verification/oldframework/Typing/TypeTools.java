package aprove.verification.oldframework.Typing;
import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Typetools contains various small helper methods to construct and
 * manipulate type terms
 * @author Stephan Swiderski
 * @version $Id$
 */
public class TypeTools {
    protected static Map typeTupleSymbols; // mapping from size to the tupel symbol
    public static final Sort typeSort; // all type terms have this sort
    public static final DefFunctionSymbol arrowSymbol; // the arrow (->) for haskell types
    public static final DefFunctionSymbol applySymbol; // the apply for haskell types

    public static final DefFunctionSymbol equiSymbol;
    public static final Type equiType;        // the type of the equiSymbol
    public static final Set<Type> equiTypes; // the one type of the equiSymbol as set

    static {
        typeSort = Sort.create("Type"); // one Sort for Types
    TypeTools.typeTupleSymbols = new HashMap();
        arrowSymbol = TypeTools.createArrowSymbol();
        applySymbol = TypeTools.createApplySymbol();
        equiSymbol = TypeTools.createEquiSymbol();
        equiType = TypeTools.createEquiType();
        equiTypes = new HashSet<Type>();
    TypeTools.equiTypes.add(TypeTools.equiType);
    }

    /**
     * only for debug
     */
    public static void tests(){
        AlgebraVariable a = AlgebraVariable.create(VariableSymbol.create("a",TypeTools.typeSort));
      List<AlgebraTerm> lot = new Vector<AlgebraTerm>();
    lot.add(a);
    lot.add(a);
    lot.add(a);

        Type my = new Type(TypeTools.arrow(a,TypeTools.arrow(TypeTools.tuple(lot),TypeTools.arrow(TypeTools.tuple(lot),TypeTools.arrow(TypeTools.arrow(a,a),a)))));
//    Type my = new Type(arrow(a,arrow(tuple(lot),arrow(a,         arrow(a,a)))));
//    Type my = new Type(arrow(tuple(new Term[] {a,a}),a));
        System.out.println(my.toString());
     Set<Position> sop = my.reflexivePositions();
    Iterator it = sop.iterator();
    while (it.hasNext()){
            Position p = (Position) it.next();
        System.out.println(p.toString());
    }
    TypeContext tct = new TypeContext();
    String test = "data List a = Cons a (List a) | Nil;\n";
    test = test + "mallo :: (List b) -> b;\n";
    test = test + "Mallo <: Hallo;\n";
    test = test + "Pallo;\n";
    test = test + "pallo :: List b -> b;\n";
    //String test = "data List a = Cons a (List a) | Nil;\n";
    //test = test + "Mase :: List b -> b;\n";
    System.out.println("------------\n");
        System.out.println(test);
    System.out.println("------------\n");



    }


    /**
     * creates the type <code>(a->a->a)</code> of the equi symbol
     */
    private static Type createEquiType(){
       AlgebraVariable a = AlgebraVariable.create( VariableSymbol.create("a",TypeTools.typeSort));
       Set<AlgebraVariable> q = new HashSet<AlgebraVariable>();
       q.add(a);
       List<AlgebraTerm> lot = new Vector<AlgebraTerm>();
       lot.add(a);
       lot.add(a);
       return new Type(new TypeQuantifier(q),TypeTools.function(lot,a));
    }

    /**
     *  creates the arrow type constructor symbol
     *  only for initialize this class
     */
    private static DefFunctionSymbol createArrowSymbol(){
       Vector<Sort> vs = new Vector<Sort>();
       vs.add(TypeTools.typeSort);
       vs.add(TypeTools.typeSort);
       DefFunctionSymbol arr = DefFunctionSymbol.create("->", vs, TypeTools.typeSort);
       arr.setFixity(SyntacticFunctionSymbol.INFIXR);
       return arr;
    }

    /**
     *  creates the arrow type constructor symbol
     *  only for initialize this class
     */
    private static DefFunctionSymbol createApplySymbol(){
       Vector<Sort> vs = new Vector<Sort>();
       vs.add(TypeTools.typeSort);
       vs.add(TypeTools.typeSort);
       DefFunctionSymbol arr = DefFunctionSymbol.create("#", vs, TypeTools.typeSort);
       arr.setFixity(SyntacticFunctionSymbol.INFIXR);
       return arr;
    }

    /**
     *  creates the arrow type constructor symbol
     *  only for initialize this class
     */
    private static DefFunctionSymbol createEquiSymbol(){
       Vector<Sort> vs=new Vector<Sort>();
       vs.add(TypeTools.typeSort);
       vs.add(TypeTools.typeSort);
       DefFunctionSymbol equ = DefFunctionSymbol.create(".=.", vs, TypeTools.typeSort);
       equ.setFixity(SyntacticFunctionSymbol.INFIX);
       return equ;
    }

    /**
     * combines 2 type terms with the arrow
     * @param t1
     * @param t2
     * @return <code>(t1 -> t2)</code> as type term
     */
    public static AlgebraTerm arrow(AlgebraTerm t1,AlgebraTerm t2){
       Vector<AlgebraTerm> args=new Vector<AlgebraTerm>();
       args.add(t1);
       args.add(t2);
       return AlgebraFunctionApplication.create(TypeTools.arrowSymbol,args);
    }

    /**
     * combines 2 terms with the type equivalence
     * @param t1
     * @param t2
     * @return <code>(t1 .=. t2)</code> as term
     */
    public static AlgebraTerm equi(AlgebraTerm t1,AlgebraTerm t2){
       Vector<AlgebraTerm> args=new Vector<AlgebraTerm>();
       args.add(t1);
       args.add(t2);
       return AlgebraFunctionApplication.create(TypeTools.equiSymbol,args);
    }

    /**
     * combines an argument type list and a type to a new combined type
     * @param lt list <code>(a1, ,an)</code> of type terms
     * @param tau last type term
     * @return the tyep term <code>(a1 -> (a2 -> ... -> (an -> tau) ...))</code>
     */
    public static AlgebraTerm arrowList(List<AlgebraTerm> lt,AlgebraTerm tau){
    for (int i = lt.size()-1; i>=0; i--){
        tau = TypeTools.arrow(lt.get(i),tau);
        }
        return tau;
    }

    /**
     * gets the last type in an arrow-term i.e.
     * return <code>b</code> of <code>a1->(a2->(a3->...(an->b)...))</code>
     * @param tau term
     * @return the last term of the arrow list
     */
    public static AlgebraTerm getResultTerm(AlgebraTerm tau){
        if (tau.getSymbol() == TypeTools.arrowSymbol) { return TypeTools.getResultTerm(tau.getArgument(1));}
        return tau;
    }

    /**
     * gets argument term <code>ai</code> of <code>a1->(a2->(a3->...(an->b)...))</code>
     * @param tau term
     * @param i position
     * @return the i-th term of the arrow list
     */
    public static AlgebraTerm getArgumentAt(AlgebraTerm tau,int i){
    Position p = Position.create();
    for (int j=0;j<i;j++){ p.add(1);}
    p.add(0);
    return tau.getSubterm(p);
    }

    /**
     * gets arguments of <code>a1->(a2->(a3->...(an->b)...))</code>
     * @param tau term
     * @return the argument list <code>a1,..,an</code>
     */
    public static List<AlgebraTerm> getArguments(AlgebraTerm tau){
        if (tau.getSymbol() == TypeTools.arrowSymbol) {
       List<AlgebraTerm> args = TypeTools.getArguments(tau.getArgument(1));
       args.add(0,tau.getArgument(0));
       return args;
    } else {
       return new Vector<AlgebraTerm>();
    }
    }

    /**
     * gets arity of Term tau
     * @param tau term
     * @return arity of tau
     */
    public static int getTermArity(AlgebraTerm tau){
        if(tau.getArguments() != null){
            if(tau.getArguments().size() > 0){
                return tau.getArguments().get(0).getArguments().size();
            }
        }
        return 0;
    }

    /**
     * get a term list of <code>a1->(a2->(a3->...(an->b)...))</code>
     * @param tau term
     * @return the term list <code>a1,...,an,b</code>
     */
    public static List<AlgebraTerm> getArrowTerms(AlgebraTerm tau){
        if (tau.getSymbol() == TypeTools.arrowSymbol) {
       List<AlgebraTerm> args = TypeTools.getArrowTerms(tau.getArgument(1));
       args.add(0,tau.getArgument(0));
       return args;
    } else {
       List<AlgebraTerm> lot = new Vector<AlgebraTerm>();
       lot.add(0,tau);
       return lot;
    }
    }

    /**
     * returns true iff the given function symbol is a type tuple constructor symbol.
     * @param fsym the function symbol to test
     * @return true iff the function symbol is a type tuple constructor symbol
     */
    public static boolean isTupleSymbol(SyntacticFunctionSymbol fsym){
        return TypeTools.typeTupleSymbols.containsValue(fsym);
    }

    /**
     *  gets the tuple-symbol for a given arity.
     *  if this symbol does not exist then it will be created
     *  and saved in the map {@link #typeTupleSymbols} .
     *  @param arity the arity
     *  @return the tupleSymbol for the given arity
     */
    public static SyntacticFunctionSymbol tupleSymbol(int arity){
        Integer i = Integer.valueOf(arity);
        SyntacticFunctionSymbol ts = (SyntacticFunctionSymbol) TypeTools.typeTupleSymbols.get(i);
        if (ts == null) {
            Vector<Sort> vs = new Vector<Sort>();
            for (int j=0;j<arity;j++) {
                vs.add(TypeTools.typeSort);
            }
            ts = DefFunctionSymbol.create("@", vs, TypeTools.typeSort);
        TypeTools.typeTupleSymbols.put(i,ts);
        }
        return ts;
    }

    /**
     * transforms a list of terms to a tuple
     * @param lot a list of terms
     * @return the tuple
     */
    public static AlgebraTerm tuple(List<AlgebraTerm> lot){
        return AlgebraFunctionApplication.create(TypeTools.tupleSymbol(lot.size()),lot);
    }

    /**
     * transforms a array of terms to a tuple
     * @param lot a array of terms
     * @return the tuple
     */
    public static AlgebraTerm tuple(AlgebraTerm[] lot){
        List<AlgebraTerm> nlot = new Vector<AlgebraTerm>(Arrays.asList(lot));
        return AlgebraFunctionApplication.create(TypeTools.tupleSymbol(nlot.size()),nlot);
    }

    /**
     * transforms a tuple to a list of terms
     * @param tau a tuple
     * @return the list of terms
     */
    public static List<AlgebraTerm> unTuple(AlgebraTerm tau){
        if (!TypeTools.typeTupleSymbols.containsValue(tau.getSymbol())) {
            throw new RuntimeException("could not untuple a normale function symbol");
        }
        return ((AlgebraFunctionApplication) tau).getArguments();
    }


    /**
     * constructs the type term <code>(a1,...,an) -> b</code>
     * @param as list of parameter type term
     * @param b result type term
     * @return <code>(a1,...,an) -> b</code> or <code>b</code> if n=0
     */
    public static AlgebraTerm function(List<AlgebraTerm> as,AlgebraTerm b){
        if (as.size() == 0) {
        return b;
    } else {
            return TypeTools.arrow(TypeTools.tuple(as),b);
    }
    }

    /**
     * gets the function argument types of function type.
     * @param tau the function type
     * @return the list of function argument types
     */
    public static List<AlgebraTerm> getFunctionArgs(AlgebraTerm tau){
        if (tau.getSymbol() == TypeTools.arrowSymbol) {
            return TypeTools.unTuple(tau.getArgument(0));
    }
    return new Vector<AlgebraTerm>();
        //throw new RuntimeException("could not get arguments of non-function type");
    }

    /**
     * gets the function argument type of function type at index i.
     * @param i the index
     * @param tau the function type
     * @return the argument type at position i.
     */
    public static AlgebraTerm getFunctionArgAt(AlgebraTerm tau, int i){
        return TypeTools.getFunctionArgs(tau).get(i);
    }

    /**
     * construct the type term for a selector out of a type term
     * @param tau the type term of a constructor
     * @param i the index of the argument for creating the selector for
     * @return the type term of this selector
     */
    public static AlgebraTerm createSelTerm(AlgebraTerm tau,int i){
        AlgebraTerm a = TypeTools.getFunctionArgAt(tau,i);
    AlgebraTerm b = TypeTools.getResultTerm(tau);
    List<AlgebraTerm> bs = new Vector<AlgebraTerm>();
        bs.add(b);
    return TypeTools.function(bs,a);
    }

    /**
     * trans form a term to a type where all variables are quantified.
     * @param tau a term
     */
    public static Type autoQuan(AlgebraTerm tau){
         return new Type(new TypeQuantifier(tau.getVars()),tau);
    }

    /**
     * this typing framework offers different signatures(multiple types) for one symbol,
     * in case you need only one type per symbol use this function to minimize overhead.
     * A runtime exception is thrown if the set of types contain more the one type.
     * @param sot set of types
     * @return the type
     */
    public static Type toSingleType(Set<Type> sot) throws TypingException{
        if (sot == null) { return null;}
        switch (sot.size()) {
       case 0  : return null;
           case 1  : return sot.iterator().next();
       default :
           throw new TypingException("multi-type used in single-type environment");
    }
    }

    /**
     * builds a new type variable with help of a fresh variable generator.
     * @param fvg fresh variable generator
     * @return a new type variable
     */
    protected static AlgebraVariable getFreshTypeVariable(FreshVarGenerator fvg){
        return fvg.getFreshVariable("t",TypeTools.typeSort,false);
    }

    /**
     * builds a new type constructor with help of a fresh name generator
     * @param fng fresh name generator
     * @param arity the arity
     * @return a new type constructor with a new name in the frsh name generator and given arity
     */
    protected static ConstructorSymbol getFreshTypeConstructor(FreshNameGenerator fng,int arity){
        Vector<Sort> vs = new Vector<Sort>();
        for (int i = 0;i<arity;i++) { vs.add(TypeTools.typeSort);}
        String name = fng.getFreshName("DT",false);
    return ConstructorSymbol.create(name,vs,TypeTools.typeSort);
    }

    /**
     * builds a new type constructor.
     * @param name the name
     * @param arity the arity
     * @return a new type constructor with given name and given arity
     */
    public static ConstructorSymbol getTypeCons(String name,int arity){
        Vector<Sort> vs = new Vector<Sort>();
        for (int i = 0;i<arity;i++) { vs.add(TypeTools.typeSort);}
    return ConstructorSymbol.create(name,vs,TypeTools.typeSort);
    }


}
