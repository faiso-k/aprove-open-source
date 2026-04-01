package aprove.verification.oldframework.Haskell.Syntax;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Visitors.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$

 * The RawTerm represents the a HaskellTerm before some informations about
 * fixity and priority are known and it is created by the parser.
 * Later it is transfromed to HaskellTerms with correct priority and fixity (called Pixity)
 * HaskellTools.arrangeFixityPriority do much of this job.
 */
public class RawTerm extends HaskellPat.HaskellObjectSkeleton implements HaskellExp,HaskellPat  {
    HaskellPreType type;
    List<HaskellObject> objs;
    boolean lhs;


    public RawTerm(List<HaskellObject> objs){
        this.objs = objs;
        this.lhs = false;
        this.type = null;
    }

    public List <HaskellObject> getObjects(){
        return this.objs;
    }

    public int getSize(){
        return this.objs.size();
    }

    public void setType(HaskellPreType type){
       this.type = type;
    }

    public HaskellPreType getType(){
       return this.type;
    }

    public void setLHS(){
        this.lhs = true;
    }

    @Override
    public Object deepcopy(){
        RawTerm nrt = new RawTerm(Copy.deepCol(this.getObjects()));
        nrt.setType(Copy.deep(this.type));
        nrt.lhs = this.lhs;
        return this.hoCopy(nrt);
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        this.objs = this.listWalk(this.objs,hv);
        this.type = this.walk(this.type,hv);
        return hv.caseRawTerm(this);
    }


    /**
     * returns true iff this rawterm represents a basic plus pattern x+n
     * and the Plus Symbol is not sym
     */
    public boolean isCurrentPlusPat(HaskellSym sym){
        List<HaskellObject> objs = this.getObjects();
        if (objs.size()==3) {
            if (objs.get(1) instanceof Operator) {
                Operator op = (Operator) objs.get(1);
                if (op.getAtom().getSymbol() == sym) {
                    return false;
                }
                // the above only returns true for the topmost symbol, since references are compared
                if (op.getAtom().getSymbol().isPlusSym()) {
                    if (objs.get(2) instanceof IntegerLit) {
                       if (objs.get(0) instanceof Var) {
                           return true;
                       }
                    }
                }
            }
        }
        return false;
    }

    /**
     * if this rawterm represents a Plus Pattern
     * this function creates the real PlusPat Object
     */
    public HaskellObject buildPlusPat(HaskellSym sym){
        if (this.isCurrentPlusPat(sym)){
           List<HaskellObject> objs = this.getObjects();
           return new PlusPat((Var) objs.get(0),(IntegerLit) objs.get(2));
        }
        return this;
    }

    /**
     * checks if the term represents a Basic Plus Pattern without Brackets
     */
    public boolean isBasicPlusPat(){
        List<HaskellObject> objs = this.getObjects();
        if (objs.size()==3) {
            return this.isCurrentPlusPat(null);
        } else {
            if (objs.size()==1) {
               if (objs.get(0) instanceof RawTerm) {
                  return ((RawTerm)objs.get(0)).isBasicPlusPat();
               }
            }
        }
        return false;
    }

   /**
    * checks if a Basic Plus Pattern is enclosed in this RawTerm
    * this means a Brackets are around the Basic Plus Pattern
    */
    public boolean isPlusPat(){
        List<HaskellObject> objs = this.getObjects();
        if (objs.size()==1) {
           if (objs.get(0) instanceof RawTerm) {
               return ((RawTerm)objs.get(0)).isBasicPlusPat();
           }
        }
        return false;
    }


    /**
     * a RawTerm could also represent the lhs of a Function
     * in this case this function returns the top symbol
     * operator or not
     */
    public HaskellSym getDeclaredFunction(){
        HaskellSym sym = this.getFunction();
        if (sym != null) {
            if (this.isPlusPat()) {
                return null;
            }
        }
        return sym;
    }

    /**
     * get the topsymbol of this RawTerm
     * an operator or the left most of an apply stack
     */
    private HaskellSym getFunction(){
        List<HaskellObject> objs = this.getObjects();
        if (objs.size()>1) {
            for (HaskellObject obj : objs){
                if (obj instanceof Operator) {
                   Operator op = (Operator) obj;
                   if ((op.getAtom()) instanceof Var) {
                      return op.getAtom().getSymbol();
                   }
                }
            }
        } else {
            HaskellObject obj = HaskellTools.getLeftMost(objs.get(0));
            if (obj instanceof Var){
                return ((Var)obj).getSymbol();
            } else if (obj instanceof RawTerm) {
                return ((RawTerm)obj).getFunction();
            }
        }
        return null;
    }

    /**
     * interprets this RawTerm as LHS and returns the List of Patterns
     */
    public List<HaskellPat> toLHS(){
        List<HaskellPat> pats = new Vector<HaskellPat>();
        if (this.objs.size()>1) {
            Var var = null;
            List<HaskellObject> left = new Vector<HaskellObject>();
            List<HaskellObject> right = new Vector<HaskellObject>();
            for (HaskellObject obj : this.objs){
                if (obj instanceof Operator) {
                   Operator op = (Operator) obj;
                   if ((op.getAtom()) instanceof Var) {
                       if (var != null) {
                           HaskellError.output(op,"unexpected operator");
                       }
                       var = (Var) op.getAtom();
                       continue;
                   }
                }
                if (var == null) {
                   left.add(obj);
                } else {
                   right.add(obj);
                }
            }
            pats.add(var);
            pats.add((HaskellPat) HaskellTools.arrangeFixityPriority(left));
            pats.add((HaskellPat) HaskellTools.arrangeFixityPriority(right));
        } else {
            List<HaskellObject> res = HaskellTools.applyFlatten(this.objs.get(0));
            if (res.get(0) instanceof RawTerm) {
                RawTerm rt = (RawTerm) res.remove(0);
                res.addAll(0,rt.toLHS());
            }
            for (HaskellObject obj : res){
                pats.add((HaskellPat)obj);
            }
        }
        return pats;
    }

    /**
     * checks if all operators are constructors in the sub RawTerms
     * ten it transforms Plus Pattern Representing sub RawTerms in PlusPats
     */
    public void patternize(HaskellSym sym){
        PatternizeVisitor pv = new PatternizeVisitor(sym);
        this.visit(pv);
        pv.setCheck();
        this.visit(pv);
    }

    /**
     * corrects the Fixity and Pixity position of the operators
     * and also add potential type signatures to the resulting Expression
     */
    public HaskellObject correctPixity(){
        if (this.lhs) {
            return this;
        } else {
            if (this.type != null) {
                return new TypeExp((HaskellExp)HaskellTools.arrangeFixityPriority(this.objs),this.type);
            }
            return HaskellTools.arrangeFixityPriority(this.objs);
        }
    }

    /**
     *  interprets this rawTerm as TypeDecl for one variable;
     */
    public HaskellObject toTypeDecl(){
        if (this.type == null) {
           HaskellError.output(this.objs.get(0),"Type expected");
        }
        if (this.objs.size() != 1) {
           HaskellError.output(this.objs.get(1),"unexpected");
        }
        HaskellObject obj = this.objs.get(0);
        if (!(obj instanceof Var)) {
           HaskellError.output(this.objs.get(0),"variable expected");
        }
        List<Var> vars = new Vector<Var>();
        vars.add((Var)obj);
        TypeDecl td = new TypeDecl(vars,this.type);
        td.transferToken(this);
        return td;
    }

    /**
     * this methods checks if the right most expression is a RightTypeBinding
     * (let,lambda,if) and passes its type to this expression
     */
    public void shiftTypeDown(HaskellPreType type){
        HaskellObject obj = this.objs.get(this.objs.size()-1);
        if (obj instanceof RightTypeBinding) {
           ((RightTypeBinding) obj).shiftTypeDown(type);
        } else {
           this.type = type;
        }
    }
}
