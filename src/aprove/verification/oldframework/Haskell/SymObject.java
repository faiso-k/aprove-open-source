package aprove.verification.oldframework.Haskell;



/**
 * @author Stephan Swiderski
 * @version $Id$
 * XML-Bean
 * this abstract class introduce a symbol field which could be visited, thats all
 */
public abstract class SymObject extends HaskellObject.HaskellObjectSkeleton implements HaskellBean {
    HaskellSym sym;

    public SymObject(){
    }

    public SymObject(HaskellSym sym){
        this.sym = sym;
    }

    public HaskellSym getSymbol(){
        return this.sym;
    }

    public void setSymbol(HaskellSym sym){
        this.sym = sym;
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.setSymbol(this.walk(this.getSymbol(),hv));
        return this;
    }

}
