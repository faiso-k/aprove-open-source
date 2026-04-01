package aprove.verification.oldframework.Haskell;

import java.util.*;

import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * A HaskellRule is the final form of a rule of a function in Haskell.
 * the contained EntityFrame contains all VarEntity of Variables occuring in the patterns
 */
public class HaskellRule extends HaskellObject.HaskellObjectSkeleton implements EntityFrameCarrier,HaskellBean {
    protected List<HaskellPat> patterns;
    protected HaskellExp expression;
    protected EntityFrame entityFrame;

    /**
     * do not use this constructor, its only for bean convention
     */
    public HaskellRule(){
    }

    /**
     * normal constructor
     */
    public HaskellRule(EntityFrame entityFrame,List<HaskellPat> patterns, HaskellExp expression){
        this.patterns = patterns;
        this.expression = expression;
        this.entityFrame = entityFrame;
    }

    @Override
    public void setEntityFrame(EntityFrame entityFrame){
        this.entityFrame = entityFrame;
    }

    @Override
    public EntityFrame getEntityFrame(){
        return this.entityFrame;
    }

    public HaskellExp getExpression(){
        return this.expression;
    }

    public void setExpression(HaskellExp expression){
        this.expression = expression;
    }

    public List<HaskellPat> getPatterns(){
        return this.patterns;
    }

    public void setPatterns(List<HaskellPat> patterns){
        this.patterns = patterns;
    }

    @Override
    public HaskellObject deepcopy(){
        return this.hoCopy(new HaskellRule(this.entityFrame,Copy.deepCol(this.patterns),Copy.deep(this.expression)));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        hv.fcaseHaskellRule(this);
        boolean args = hv.guardArguments(this);
        if (args) {
            hv.fcaseEntityFrame(this.entityFrame);
        }
        if (hv.guardHaskellRulePatterns(this)){
            this.patterns = this.listWalk(this.patterns,hv);
        }
        hv.icaseHaskellRule(this);
        this.expression = this.walk(this.expression,hv);
        if (args) {
            hv.icaseEntityFrame(this.entityFrame);
        }
        if (hv.guardHaskellRuleEntityFrame(this)){
            this.entityFrame = this.walk(this.entityFrame,hv);
        }
        return hv.caseHaskellRule(this);
    }

    /**
     * @returns true, iff this rule is simple pattern binding (like: f = 5)
     */
    public boolean isSimplePattern(){
        return this.patterns.size()==0;
    }

    /**
     * @returns true, iff this rule has conditions
     */
    public boolean isConditional(){
        return (this.expression instanceof CondStackExp);
    }

}
