package aprove.verification.oldframework.Haskell;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 */
public class HaskellSubstitution extends HashMap<HaskellSym, HaskellObject> {

    transient int currentSubtermIDMax = 0;

    /**
     * do not use this constructor, its only for bean convention
     */
    public HaskellSubstitution(){
        super();
    }

    /**
     * several normal constructors
     */
    public HaskellSubstitution(Collection<Pair<BasicTerm,BasicTerm>> col){
        super();
        for (Pair<BasicTerm,BasicTerm> pair : col){
            Var var = (Var) pair.getKey();
            this.put(var.getSymbol(),pair.getValue());
        }
    }

    /**
     * creates a substitution with one replacement given as pair
     */
    public HaskellSubstitution(Pair<BasicTerm,BasicTerm> pair){
        super();
        Var var = (Var) pair.getKey();
        this.put(var.getSymbol(),pair.getValue());
    }

    /**
     * creates a substitution with one replacement given directly
     */
    public HaskellSubstitution(Var var,BasicTerm term){
        super();
        this.put(var.getSymbol(),term);
    }

    /**
     * creates a substitution with one replacement given directly
     */
    public HaskellSubstitution(HaskellSym sym,BasicTerm term){
        super();
        this.put(sym,term);
    }

    /**
     * creates a new substitution which maps the variables in the quantor
     * to fresh ones
     */
    public HaskellSubstitution(Quantor quantor){
        super();
        for (HaskellSym sym : quantor){
           this.put(sym,Var.createFreshVar());
        }
    }

    /**
     * applies this Substitution to the given term and possibly change it
     */
    public BasicTerm applyToDestructive(BasicTerm term){
        return (BasicTerm)term.visit(new VarSubstitutor(this));
    }

    /**
     * applies this Substitution to the given term and returns the result
     */
    public BasicTerm applyTo(BasicTerm term){
        return this.applyToDestructive(Copy.deep(term));
    }


    /**
     * applies the substitution to the given term, where currentMax is the maximum of all subtermIDs in term
     */
    public BasicTerm applyToWithSubtermNumbering(BasicTerm term, int currentMax) {
        this.currentSubtermIDMax = currentMax;
        return (BasicTerm)Copy.deep(term).visit(new VarSubstitutorWithSubtermNumbering(this));
    }

    public int getNewSubtermIDMax() {
        return this.currentSubtermIDMax;
    }

    /**
     * returns the current maximal subterm id and increments it thereafter by one
     */
    public int incSubtermIDMax() {
        return this.currentSubtermIDMax++;
    }

    /**
     * driect access to the replacements by the symbol
     */
    public HaskellObject getReplaceFor(HaskellSym sym){
        return this.get(sym);
    }

    /**
     * driect access to the replacements by the symbol of the variable
     */
    public HaskellObject getReplaceFor(Var var){
        return this.getReplaceFor(var.getSymbol());
    }

    /**
     * removes some symbols form the domain
     */
    public void removeAll(Set<HaskellSym> syms){
        for (HaskellSym sym : syms){
            this.remove(sym);
        }
    }


    /**
     * removes all occurences of the form x/x
     * @return this
     */
    public HaskellSubstitution eliminateDuplicates() {
        Iterator<Map.Entry<HaskellSym, HaskellObject>> sym_it = this.entrySet().iterator();
        while (sym_it.hasNext()) {
            Map.Entry<HaskellSym, HaskellObject> e = sym_it.next();
            HaskellSym sym = e.getKey();
            HaskellObject ho = e.getValue();
            if ( (ho instanceof Var) && (((Var)ho).getSymbol().equals(sym)) ) {
                sym_it.remove();
            }
        }
        return this;
    }


    /**
     * combine the given substitution with this one
     * to a new one
     * new(x) = subs(this(x))
     */
    public HaskellSubstitution combineWith(HaskellSubstitution subs){
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("A-----------------------------");
            //System.out.println(this+" combine ");
            //System.out.println(subs+" ======");
        }

        HaskellSubstitution nsub = new HaskellSubstitution();
        nsub.putAll(subs); ///new(x) = subs(x) if this(x)=x (x not in dom(this))
        // work through the domain of this and set new(x) = subs(this(x)) if x in dom(this)
        for (Map.Entry<HaskellSym,HaskellObject> e : this.entrySet()){
            nsub.put(e.getKey(),subs.applyTo((BasicTerm)e.getValue()));
    }
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println(nsub);
            //System.out.println("B-----------------------------");
        }

        return nsub;
    }

    @Override
    public String toString(){
        String r ="";
        for (Map.Entry e : this.entrySet()){
        String info = "";
        /*if (this.conMap != null){
            info = ""+this.conMap.get(e.getKey());
        } */
            r = r + e.getKey()+" -> "+e.getValue()+ "  |  "+info+ " \n";
    }
        return r;
    }

    public String export(Export_Util eu,Module module){
        StringBuffer r = new StringBuffer();
        boolean first = true;
        for (Map.Entry<HaskellSym,HaskellObject> e : this.entrySet()){
            if (!first){
                r.append(eu.linebreak());
            }
            r.append(eu.haskellObject(new Var(e.getKey()),module));
            r.append("/");
            r.append(eu.haskellObject(e.getValue(),module));
            first = false;
        }
        return r.toString();
    }

}
