package aprove.verification.oldframework.Haskell.Literals;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Patterns.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * CharLit represents a character literal of a Haskell program.
 */
public class CharLit extends HaskellPat.HaskellObjectSkeleton implements HaskellLit {
    char charValue;

    public CharLit(){
    }

    public CharLit(char charValue){
        this.charValue = charValue;
    }

    public char getCharValue(){
        return this.charValue;
    }

    public void setCharValue(char charValue){
        this.charValue = charValue;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new CharLit(this.getCharValue()));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        return hv.caseCharLit(this);
    }

}
