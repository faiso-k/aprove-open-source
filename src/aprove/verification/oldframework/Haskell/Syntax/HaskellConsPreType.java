package aprove.verification.oldframework.Haskell.Syntax;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * HaskellPreType is the pre-Typeschema form of a type of a Haskellprogram and
 * it contains a context and a matrix, if it contains Variables thier HaskellSymbols
 * are need to go through TyVarTransformerVisitor, the methode toTypeSchema does that all.
 */

public class HaskellConsPreType extends HaskellPreType {
    List<HaskellObject> paramTypes;

    public HaskellConsPreType(Context context,HaskellObject matrix,EntityFrame entityFrame,List<HaskellObject> paramTypes){
        super(context,matrix,entityFrame);
        this.paramTypes = paramTypes;
    }

    public HaskellConsPreType(Context context,HaskellObject matrix,List<HaskellObject> paramTypes){
        this(context,matrix,null,paramTypes);
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new HaskellConsPreType(Copy.deep(this.context),Copy.deep(this.matrix),this.entityFrame,Copy.deepCol(this.paramTypes)));
    }

    @Override
    public TypeSchema toTypeSchema(Set<HaskellBasicRule> typeRules){
        TyVarTransformerVisitor tvtv = new TyVarTransformerVisitor();
        Context nContext = this.walk(Copy.deep(this.context),tvtv);
        HaskellObject nMatrix = this.walk(Copy.deep(this.matrix),tvtv);
        List<HaskellObject> nParamTypes = this.listWalk(Copy.deepCol(this.paramTypes),tvtv);
        Set<ClassConstraint> ccs = new HashSet<ClassConstraint>();
        Set<HaskellSym> syms = new HashSet<HaskellSym>();
        Set<HaskellSym> csyms = new HashSet<HaskellSym>();
        this.listWalk(nParamTypes,new FreeVarSymCollector(syms));
        for (ClassConstraint cc : nContext.toClassConstraints()){
            csyms.clear();
            cc.visit(new FreeVarSymCollector(csyms));
            if (syms.containsAll(csyms)){
                ccs.add(cc);
            }
        }
        if (!ClassConstraintGraph.constraintsInWHNF(ccs)){
            HaskellError.output(this,"illegal constraints "+ccs);
        }
        TypeSchema ts;
        ts = new TypeSchema(tvtv.getQuantor(),ccs,(HaskellType)nMatrix);
        BasicRuleApplyVisitor brav = new BasicRuleApplyVisitor(typeRules);
        do {
           ts.visit(brav);
        } while (brav.wasActive());
        return ts;
    }
}
