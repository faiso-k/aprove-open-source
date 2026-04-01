package aprove.verification.oldframework.Haskell;

import java.util.*;

import aprove.verification.oldframework.Utility.*;



/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This class represents the final form of a function.
 * prefroms are PreFunction or InstPreFunction and FuncDecl
 * HaskellBean
 */
public class Function extends SymObject implements HaskellBean {

    List <HaskellRule> rules;

    /**
     * do not use this constructor, its only for bean convention
     */
    public Function(){
    }

    /**
     * normal constructor
     */
    public Function(HaskellSym sym,List <HaskellRule> rules){
        super(sym);
        this.rules = rules;
    }

    public List <HaskellRule> getRules(){
        return this.rules;
    }

    public void setRules(List <HaskellRule> rules){
        this.rules = rules;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new Function(Copy.deep(this.getSymbol()),Copy.deepCol(this.rules)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseFunction(this);
        this.setSymbol(this.walk(this.getSymbol(),hv));
        this.rules = this.listWalk(this.rules,hv);
        return hv.caseFunction(this);
    }

    /**
     * returns true iff it contains only one rule which represents a simple pattern
     */
    public boolean isSimplePattern(){
        return this.rules.get(0).isSimplePattern();
    }

    /**
     * returns true iff a rule inside has conditions
     */
    public boolean hasConditions(){
       for (HaskellRule rule : this.rules){
           if (rule.isConditional()) {
            return true;
        }
       }
       return false;
    }
}
