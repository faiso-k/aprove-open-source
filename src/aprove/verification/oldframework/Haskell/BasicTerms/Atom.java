package aprove.verification.oldframework.Haskell.BasicTerms;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Typing.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * An atom is potentially a basicterm, a pattern, an expression, an import and a type
 * of haskellprogram, i.e. haskell variables and constructors are atoms
 * XML-Bean
 */
public abstract class Atom extends SymObject implements HaskellBean,HaskellExp,HaskellPat,HaskellImport,HaskellExport,BasicTerm,HaskellType {

    /**
     * fullfill the bean convention
     */
    public Atom(){
        super();
    }

    /**
     * use this constructor
     */
    public Atom(HaskellSym sym){
        super(sym);
    }

    /**
     * sets the entity of an Atom by its name and sort
     * by consideration of the local context given by the EntityFrame
     */
    public abstract void setEntityPer(EntityFrame ef);

    /**
     * direct sort setter HaskellASTBuilder
     * a QCNAME occurs in an Export List oder ImportSpec
     * An atom get this information directly by the HaskellASTBuilder
     */
    public abstract void setQCNAME();

    /**
     * equivalence check for matching and so on
     * only structurally
     * (interface BasicTerm)
     */
    @Override
    public boolean equivalentTo(BasicTerm t){
       if (t.getBasicSort() == this.getBasicSort()){
           Atom atom = (Atom) t;
           return (atom.getSymbol().equivalentTo(this.getSymbol()));
       }
       return false;
    }


}
