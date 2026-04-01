/**
 *
 */
package aprove.verification.oldframework.Haskell.Evaluator;

import aprove.verification.oldframework.Haskell.*;

public class TermResult extends NENMIResult {
    HaskellObject term;
    int subtermID;

    public TermResult(HaskellObject term,int subtermID){
        this.setTerm(term);
        this.setSubtermID(subtermID);
    }

    @Override
    public ResultKind getKind(){
        return ResultKind.TERM;
    }

    public HaskellObject getTerm(){
        return this.term;
    }

    public int getSubtermID(){
        return this.subtermID;
    }

    public void setTerm(HaskellObject term){
        this.term = term;
    }

    public void setSubtermID(int subtermID){
        this.subtermID = subtermID;
    }

}