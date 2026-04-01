/*
 * Created on 30.10.2005
 */
package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;
import immutables.*;


/**
 * A condition is a pair of terms s,t
 * which have to be in some relation to be fulfilled.
 * This relation is indicated by the type flag.
 *
 * @author matraf
 *
 */
public class Condition implements Immutable, Exportable, HasFunctionSymbols, HasVariables, HasTRSTerms, CPFAdditional {

    public static enum ConditionType {EQUAL, JOIN, ARROW};

    /**
     * maps a ConditionType to a String representation
     */
    public static String getRelSymbol(ConditionType type, Export_Util eu) {
        switch(type) {
            case EQUAL: return "=";
            case ARROW: return eu.rightarrow();
            case JOIN: return "-><-";
            default: throw new RuntimeException("ERROR: unknown condition type");
        }
    }


    /**
     * maps a ConditionType to a String representation
     */
    public static String getRelSymbol(ConditionType type) {
        return Condition.getRelSymbol(type, new PLAIN_Util());
    }




    // stored values
    private final TRSTerm s,t;
    private final ConditionType type;

    private final int hashCode;

    private static boolean checkProperTerms(TRSTerm s, TRSTerm t) {
        return s != null
        && t != null
        ;
    }

     protected Condition(TRSTerm s, TRSTerm t, ConditionType type) {
         if (aprove.Globals.useAssertions) {
             assert(Condition.checkProperTerms(s,t));
         }
         this.s = s;
         this.t = t;
         this.type = type;

         this.hashCode = 490321*s.hashCode() + 12812*t.hashCode() + 312038193*Condition.getRelSymbol(type).hashCode();
    }


    /**
     * creates a new condition
     *
     * @param s
     * @param t
     * @param type
     */
    public static Condition create(TRSTerm s, TRSTerm t, ConditionType type) {
        return new Condition(s,t,type);
    }


    @Override
    public int hashCode() {
        return this.hashCode;
    }

    /**
     * returns true iff two conditions are equal
     */
    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof Condition) {
            Condition cond = (Condition) other;
            return (this.hashCode == cond.hashCode) && (this.type.equals(cond.type)) && (this.s.equals(cond.s)) && (this.t.equals(cond.t));
        }
        return false;
    }


    /**
     * returns the set of variables that occur in this condition
     */
    @Override
    public ImmutableSet<TRSVariable> getVariables() {
        Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>(this.s.getVariables());
        vars.addAll(this.t.getVariables());
        return ImmutableCreator.create(vars);
    }



    /**
     * returns the set of functionSymbols occurring in this rule
     */
    @Override
    public ImmutableSet<FunctionSymbol> getFunctionSymbols() {
        Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>(this.s.getFunctionSymbols());
        fs.addAll(this.t.getFunctionSymbols());
        return ImmutableCreator.create(fs);
    }


    /**
     * returns the lhs of the condition
     */
    public TRSTerm getLeft() {
        return this.s;
    }

    /**
     * returns the rhs of the condition
     */
    public TRSTerm getRight() {
        return this.t;
    }

    /**
     * returns the type of this condition
     */
    public ConditionType getType() {
        return this.type;
    }


    /**
     * returns the set of terms of this condition,
     * i.e. the set {s,t} for a condition s = t
     */
    @Override
    public Set<TRSTerm> getTerms() {
        Set<TRSTerm> terms = new LinkedHashSet<TRSTerm>();
        terms.add(this.s);
        terms.add(this.t);
        return terms;
    }



    @Override
    public String export(Export_Util eu) {
        return this.getLeft().export(eu) + " " + Condition.getRelSymbol(this.type, eu) + " " + this.getRight().export(eu);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }


    @Override
    public Element toCPF(Document doc, XMLMetaData xmlMetaData) {
        return CPFTag.CONDITION.create(doc,
            CPFTag.LHS.create(doc, this.s.toCPF(doc, xmlMetaData)),
            CPFTag.RHS.create(doc, this.t.toCPF(doc, xmlMetaData)));
    }


}
