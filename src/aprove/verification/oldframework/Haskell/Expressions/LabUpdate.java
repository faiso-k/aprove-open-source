package aprove.verification.oldframework.Haskell.Expressions;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 * LabUpdate represents a record update expression
 * currently this is not used
 */
public class LabUpdate extends HaskellObject.HaskellObjectSkeleton implements HaskellExp,HaskellBean {
    HaskellExp expression;
    List<FieldEqu> fieldEquations;

    /**
     * do not use this constructor, its only for bean convention
     */
    public LabUpdate(){
    }

    /**
     *  normal constructor
     */
    public LabUpdate(HaskellExp expression, List<FieldEqu> fieldEquations){
        this.expression = expression;
        this.fieldEquations = fieldEquations;
    }

    public List<FieldEqu> getFieldEquations(){
        return this.fieldEquations;
    }

    public void setFieldEquations(List<FieldEqu> fieldEquations){
        this.fieldEquations = fieldEquations;
    }

    public HaskellExp getExpression(){
        return this.expression;
    }

    public void setExpression(HaskellExp expression){
        this.expression = expression;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new LabUpdate(Copy.deep(this.expression),Copy.deepCol(this.fieldEquations)));
    }

    @Override
    public String toString() {
        return this.expression + " { "+this.fieldEquations+" } ";
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseLabUpdate(this);
        this.expression = this.walk(this.expression,hv);
        this.fieldEquations = this.listWalk(this.fieldEquations,hv);
        return hv.caseLabUpdate(this);
    }

}
