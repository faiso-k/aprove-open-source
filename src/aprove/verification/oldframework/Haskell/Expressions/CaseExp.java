package aprove.verification.oldframework.Haskell.Expressions;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * XML-Bean
 * represents a case-expression
 * contains the case-alternatives
 */

public class CaseExp extends HaskellObject.HaskellObjectSkeleton implements HaskellExp,HaskellBean {
    protected HaskellExp argument;
    protected List<AltExp> cases;

    /**
     * do not use this constructor, its only for bean convention
     */
    public CaseExp(){
    }

    /**
     * normal constructor
     */
    public CaseExp(HaskellExp argument, List<AltExp> cases){
        this.argument = argument;
        this.cases = cases;
    }

    public List<AltExp> getCases(){
        return this.cases;
    }

    public void setCases(List<AltExp> cases){
        this.cases = cases;
    }

    public HaskellExp getArgument(){
        return this.argument;
    }

    public void setArgument(HaskellExp argument){
        this.argument = argument;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new CaseExp(Copy.deep(this.getArgument()),Copy.deepCol(this.getCases())));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseCaseExp(this);
        this.argument = this.walk(this.argument,hv);
        this.cases = this.listWalk(this.cases,hv);
        return hv.caseCaseExp(this);
    }

}
