package aprove.verification.oldframework.Haskell.Syntax;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * LabCons represents a constructor with its parameters given as FieldEquations
 * for Haskell Records
 * this is currently ignored and not used
 */
public class LabCons extends HaskellPat.HaskellObjectSkeleton implements HaskellExp,HaskellPat {
    Cons cons;
    List<FieldEqu> equs;

    public LabCons(Cons cons, List<FieldEqu> equs){
        this.cons = cons;
        this.equs = equs;
    }

    public List<FieldEqu> getFieldEquations(){
        return this.equs;
    }

    public Cons getCons(){
        return this.cons;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new LabCons(Copy.deep(this.cons),Copy.deepCol(this.equs)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseLabCons(this);
        this.cons = this.walk(this.cons,hv);
        this.equs = this.listWalk(this.equs,hv);
        return hv.caseLabCons(this);
    }


    @Override
    public String toString() {
        return this.cons + " { "+ this.equs + " } ";
    }
}
