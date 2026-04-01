package aprove.verification.oldframework.LinearArithmetic;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * Does some simplification on linear terms.
 * For each variable the sum of all occurences is counted.
 * A constant is calculated.
 * It is respected on which side variables or constants occure.
 *
 * It is assumed that linear terms are (in)equalities of the form:
 * a*x + b*y + ... (<,>,=,<=,>=,!=) k
 * But it is also possible that they have the form
 * a*x + b*y + ... + k
 * In this case the constant k is multiplied by (-1)
 *
 * @author dickmeis
 * @version $Id$
 */


public class LinearTermNormalizer implements FineGrainedTermVisitor<Object>{

    private int constant;
    private Map<AlgebraVariable, Integer> coefficients;
    private ConstraintType constraintType;
    private boolean linearTerm;

    private boolean not;
    private boolean top;
    private boolean plus;

    private LAProgramProperties laProgram;

    /**
     * Constructor for a LinearTermNormalizer
     *
     * @param laProgram Background information about the properties of LA
     */
    public LinearTermNormalizer(LAProgramProperties laProgram){
        this.laProgram = laProgram;
        this.coefficients = new LinkedHashMap<AlgebraVariable, Integer>();
        this.plus = true;
        this.constraintType = null;
        this.linearTerm = true;
        this.top=true;
        this.not=false;
    }

    /**
     * Get the parsed linear constraint
     *
     * @return the parsed linear constraint
     */
    public LinearConstraint getConstraint(){
        if (!this.linearTerm){
            return null;
        }
        else if (this.constraintType == null){
            return null;
        }
        else{
            return new LinearConstraint(this.coefficients, this.constraintType, this.constant);
        }
    }

    @Override
    public Object caseConstructorApp(ConstructorApp cterm) {
        ConstructorSymbol cs = cterm.getConstructorSymbol();
        if (cs.equals(this.laProgram.csSucc)){
            this.top=false;
            if (this.plus){
                this.constant--;
            }
            else{
                this.constant++;
            }
            AlgebraTerm t = cterm.getArgument(0);
            t.apply(this);
        }
        else if (cs.equals(this.laProgram.csZero)){
            this.top=false;
        }
        else{
            // not a linear term
            this.linearTerm = false;
        }
        return null;
    }

    @Override
    public Object caseDefFunctionApp(DefFunctionApp fterm){
        DefFunctionSymbol dfs = fterm.getDefFunctionSymbol();
        if (dfs.equals(this.laProgram.fsPlus)){
            this.top=false;
            for (AlgebraTerm t: fterm.getArguments()) {
                t.apply(this);
            }
        }
        else if (dfs.equals(this.laProgram.fsNot)){
            if (!this.top){
                // not is not allowed deep inside a term tree
                // only at root or directly after another legal not
                this.linearTerm = false;
                return null;
            }

            if(this.not){
                this.not = false;
            }
            else{
                this.not = true;
            }

            AlgebraTerm t = fterm.getArgument(0);
            t.apply(this);
        }
        else {
            if (dfs.equals(this.laProgram.fsLess)){
                if(this.not){
                    this.setConstraintType(ConstraintType.GREATEREQ);
                }
                else{
                    this.setConstraintType(ConstraintType.LESS);
                }
            }
            else if (dfs.equals(this.laProgram.fsLesseq)){
                if(this.not){
                    this.setConstraintType(ConstraintType.GREATER);
                }
                else{
                    this.setConstraintType(ConstraintType.LESSEQ);
                }
            }
            else if (dfs.equals(this.laProgram.fsGreater)){
                if(this.not){
                    this.setConstraintType(ConstraintType.LESSEQ);
                }
                else{
                    this.setConstraintType(ConstraintType.GREATER);
                }
            }
            else if (dfs.equals(this.laProgram.fsGreatereq)){
                if(this.not){
                    this.setConstraintType(ConstraintType.LESS);
                }
                else{
                    this.setConstraintType(ConstraintType.GREATEREQ);
                }
            }
            else if (dfs.equals(this.laProgram.fsEqual)){
                if(this.not){
                    this.setConstraintType(ConstraintType.INEQUALITY);
                }
                else{
                    this.setConstraintType(ConstraintType.EQUALITY);
                }
            }
            else if (dfs.equals(this.laProgram.fsInequal)){
                if(this.not){
                    this.setConstraintType(ConstraintType.EQUALITY);
                }
                else{
                    this.setConstraintType(ConstraintType.INEQUALITY);
                }
            }
            else{
                // not a linear term
                this.linearTerm = false;
                return null;
            }
            this.top=false;
            AlgebraTerm t = fterm.getArgument(0);
            t.apply(this);

            this.inverse();
            t = fterm.getArgument(1);
            t.apply(this);
            this.inverse();
        }

        return null;
    }

    @Override
    public Object caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {
        return null;
    }

    @Override
    public Object caseVariable(AlgebraVariable v) {
        this.top=false;

        Integer i = this.coefficients.get(v);

        if(i == null){
            i=0;
        }

        if (this.plus){
            i++;
        }
        else{
            i--;
        }
        this.coefficients.put(v,i);

        return null;
    }

    private void inverse(){
        if(this.plus){
            this.plus = false;
        }
        else{
            this.plus = true;
        }
    }

    /**
     * Sets the ConstraintType.
     * Detects if this is not a term representing a linear constraint
     *
     * @param constraintType the ConstraintType to set.
     */
    private void setConstraintType(ConstraintType constraintType) {
        if (this.constraintType == null){
            this.constraintType = constraintType;
        }
        else {
            // ConstraintType already set
            this.linearTerm = false;
        }
    }

    /**
     * Says if the parsed term is a linear term
     *
     * @return true iff the parsed term is a linear term
     */
    public boolean isLinearTerm(){
        return this.linearTerm;
    }

    @Override
    public String toString() {

        if(! this.linearTerm){
            return("Not a linear term.");
        }

        StringBuilder sb = new StringBuilder();

        Iterator<Entry<AlgebraVariable, Integer>> i = this.coefficients.entrySet().iterator();
        if (i.hasNext()){
            Entry<AlgebraVariable, Integer> e = i.next();
            sb.append(e.getValue());
            sb.append("*");
            sb.append(e.getKey().getName());
        }
        else{
            sb.append("0");
        }

        while (i.hasNext()){
            Entry<AlgebraVariable, Integer> e = i.next();

            sb.append(" + ");

            sb.append(e.getValue());
            sb.append("*");
            sb.append(e.getKey().getName());
        }

        if(this.constraintType == null){
            sb.append(" + " + (-1*this.constant));
        }
        else{
            sb.append(" " + this.constraintType + " ");
            sb.append(this.constant);
        }

        return sb.toString();
    }

    /**
     * @return the coefficients
     */
    public Map<AlgebraVariable, Integer> getCoefficients() {
        Map<AlgebraVariable, Integer> coefficientsCopy = new LinkedHashMap<AlgebraVariable, Integer>(this.coefficients.size());
        for (Entry<AlgebraVariable, Integer> entry : this.coefficients.entrySet()) {
            coefficientsCopy.put(entry.getKey(), entry.getValue());
        }
        return coefficientsCopy;
    }

    /**
     * @return the constant
     */
    public int getConstant() {
        return this.constant;
    }

    /**
     * @return the constraintType
     */
    public ConstraintType getConstraintType() {
        return this.constraintType;
    }

}
