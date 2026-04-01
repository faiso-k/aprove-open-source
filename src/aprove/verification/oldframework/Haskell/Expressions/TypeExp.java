package aprove.verification.oldframework.Haskell.Expressions;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * XML-Bean
 * represents a the type signature expression for one expression (exp :: type)
 * first it contains a HaskellPreType which is later transformed to a typeschema
 */
public class TypeExp extends HaskellObject.HaskellObjectSkeleton implements HaskellBean,HaskellExp {
    HaskellExp expression;
    TypeSchema typeSchema;
    transient HaskellPreType type;

    /**
     * do not use this constructor, its only for bean convention
     */
    public TypeExp(){
    }

    /**
     * constructor for deepcopy
     */
    public TypeExp(HaskellExp expression, HaskellPreType type,TypeSchema typeSchema) {
         this.type = type;
         this.expression = expression;
         this.typeSchema = typeSchema;
    }

    /**
     * normal constructor
     */
    public TypeExp(HaskellExp expression, HaskellPreType type) {
         this.type = type;
         this.expression = expression;
         this.typeSchema = null;
    }

    public void setExpression(HaskellExp expression){
         this.expression = expression;
    }

    public HaskellExp getExpression(){
         return this.expression;
    }

    public HaskellPreType getPreType(){
         return this.type;
    }

    public TypeSchema getTypeSchema(){
         return this.typeSchema;
    }

    public void setTypeSchema(TypeSchema typeSchema){
         this.typeSchema = typeSchema;
    }

    @Override
    public Object deepcopy(){
        return this.hoCopy(new TypeExp(Copy.deep(this.getExpression()),Copy.deep(this.type),Copy.deep(this.typeSchema)));
    }

    /**
     * transform the HaskellPreType to a TypeSchema by using some typeRules
     */
    public void buildTypeSchema(Set<HaskellBasicRule> typeRules){
        this.typeSchema = this.type.toTypeSchema(typeRules);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.expression = this.walk(this.expression,hv);
        if (hv.guardTypeTypeExp(this)) {
            this.type = this.walk(this.type,hv);
        }
        if (hv.guardTypeSchemaTypeExp(this)) {
            this.typeSchema = this.walk(this.typeSchema,hv);
        }
        return hv.caseTypeExp(this);
    }

}
