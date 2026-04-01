package aprove.verification.oldframework.Typing;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * A <code>TypeAssumption</code> is a mapping from symbols to their set of types.
 * A symbol could have multiple types.
 * For single type environment use the special methods setSingleType and getSingleType
 * (they will raise exceptions if a multiple type occurs accidentally).
 * @author Stephan Swiderski
 * @version $Id$
 */

public interface TypeAssumption extends java.io.Serializable{

    /**
     * @return the set of declared symbols
     */
    public Set<Symbol> getDeclaredSymbols();

    /**
     * Adds a type declaration <code>(sym:t1/.../tn)</code> to this type assumption.
     * @param sym symbol
     * @param taus dedicated set of type
     */
    public Set<Type> getTypesOf(Symbol sym);

    /**
     * returns the assumed type of a symbol.
     * @param sym
     * @return a the type for the function, constructor or variable symbole sym
     */
    public Type getSingleTypeOf(Symbol sym) throws TypingException;

    public void setSingleTypeOf(Symbol sym,Type tau) throws TypingException;

    public void setTypesOf(Symbol sym,Set<Type> taus) throws TypingException;

    public Collection<Set<Type>> getRange();


    public class TypeAssumptionSkeleton implements TypeAssumption {

        protected Map<Symbol, Set<Type>> typeMap;  // assumptions, a mapping from symbols to types

        /**
         *  Construct an empty type assumption.
         */
        public TypeAssumptionSkeleton() {
           this.typeMap = new HashMap<Symbol,Set<Type>>();
        }

        /**
         *  Construct a type assumption with given tymap
         *  @param tymap (changing tymap results in changing this type assumption)
         */
        public TypeAssumptionSkeleton(Map<Symbol,Set<Type>> tymap) {
           this.typeMap = tymap;
        }

        /**
         * Adds type declaration of the form sym:freshvar for some symbols
         * @param fvg for fresh type vars
         * @param syms set of symbols
         */
        public void addWithFreshTypeVars(FreshVarGenerator fvg,Set< ? extends Symbol> syms){
           Iterator it = syms.iterator();
           for(Symbol csym : syms) {
              Type ct = new Type(new TypeQuantifier(),TypeTools.getFreshTypeVariable(fvg));
              Set<Type> sot = new HashSet<Type>();
              sot.add(ct);
              this.setTypesOf(csym,sot);
           }
        }

        /**
         * Adds type quantifier (for all free variables) to the type
         * declaration of some symbols.
         * @param syms set of symbols
         */
        public void addQuantifier(Set<Symbol> syms) {
            for (Symbol csym : syms) {
                Set<Type> sot = new HashSet<Type>();
                for (Type type : this.getTypesOf(csym)) {
                    AlgebraTerm tt = type.getTypeMatrix();
                    sot.add(new Type(new TypeQuantifier(tt.getVars()), tt));
                }
                this.setTypesOf(csym, sot);
            }
        }

        /**
         * @return the set of declared symbols
         */
        @Override
        public Set<Symbol> getDeclaredSymbols() {
            return new HashSet<Symbol>(this.typeMap.keySet());
        }

        /**
         * returns the assumed set of types <code>(t1/.../tn)</code> of a symbol.
         * @param sym
         * @return a set of types for the function, constructor or variable symbole sym
         */
        @Override
        public Set<Type> getTypesOf(Symbol sym) {
            if (sym == TypeTools.equiSymbol) { return TypeTools.equiTypes; }
            return (Set<Type>) this.typeMap.get(sym);
        }

        /**
         * returns the assumed type of a symbol.
         * @param sym
         * @return a the type for the function, constructor or variable symbole sym
         */
        @Override
        public Type getSingleTypeOf(Symbol sym) throws TypingException {
            return TypeTools.toSingleType(this.getTypesOf(sym));
        }

        /**
         * Adds a type declaration <code>(sym:t1/.../tn)</code> to this type assumption.
         * @param sym symbol
         * @param taus dedicated set of type
         */
        @Override
        public void setTypesOf(Symbol sym,Set<Type> taus){
            this.typeMap.put(sym,taus);
        }

        /**
         * Adds a type declaration <code>(sym:tau)</code> to this type assumption.
         * @param sym symbol
         * @param tau dedicated type
         */
        @Override
        public void setSingleTypeOf(Symbol sym,Type tau){
            Set<Type> sot = new HashSet<Type>();
            sot.add(tau);
            this.setTypesOf(sym, sot);
        }

        /**
         * Removes a type declaration <code>(sym:tau)</code> from this type assumption.
         * @param sym symbol
         */
        public void removeTypesOf(Symbol sym){
            this.typeMap.remove(sym);
        }


        /**
         * Construct a deep copy of this type assumption in the same {@link TypeContext}.
         * @return a new type assumption
         */
        public TypeAssumption.TypeAssumptionSkeleton deepcopy() {
            TypeAssumptionSkeleton nTA = new TypeAssumptionSkeleton();
            for(Map.Entry<Symbol,Set<Type>> entry : this.typeMap.entrySet()) {
                Set<Type> sot = new HashSet<Type>();
                for(Type type: entry.getValue()) {
                    sot.add(type.deepcopy());
                }
                nTA.setTypesOf((Symbol)entry.getKey(),sot);
            }
            return nTA;
        }

        @Override
        public Collection  getRange() {
            return this.typeMap.values();
        }
        /*
         * @return a string representation of this object
         */
        @Override
        public String toString(){
            String res = "\n";
            String line = new String("/");
            for (Map.Entry<Symbol, Set<Type>> entry : this.typeMap.entrySet()) {
                Symbol csym = entry.getKey();
                res = res + csym.toString() + " :: ";
                for (Type type : entry.getValue()) {
                    String was = " ";
                    res = res + was + type.toString();
                    was = line;
                }
                res = res + "\n";
            }
            return res + "\n";
        }

        public Map getTypeMap() {
            return this.typeMap;
        }

        public void setTypeMap(Map<Symbol,Set<Type>> typeMap) {
            this.typeMap = typeMap;
        }

    }

}

