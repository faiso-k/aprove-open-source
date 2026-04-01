package aprove.verification.oldframework.Haskell.Visitors;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Syntax.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * this visitor checks if a HaskellObject is a correct formed pattern
 * (all used operators are constructors, and variables are first order)
 *
 */
public class PatternizeVisitor extends HaskellVisitor{
    HaskellSym sym;
    boolean check;

    public PatternizeVisitor(HaskellSym sym){
        this.sym = sym;
        this.check = false;
    }

    public void setCheck(){
        this.check = true;
    }

    @Override
    public void fcaseApply(Apply ho){
        if (ho.getFunction() instanceof Var){
           Var var = (Var) ho.getFunction();
           if (var.getSymbol()!=this.sym) {
               // var is higher order
               HaskellError.output(ho.getArgument(),"unexpected");
           }
        }
    }

    @Override
    public HaskellObject caseOperator(Operator op) {
        if (!this.check) {
            return op;
        }
        if (op.getAtom() instanceof Var) {
            if (op.getAtom().getSymbol() != this.sym) {
                HaskellError.output(op,"constructor expected");
            }
        }
        return op;
    }

    @Override
    public HaskellObject caseRawTerm(RawTerm rt) {
        if (this.check) {
            return rt;
        }
        return rt.buildPlusPat(this.sym);
    }
}
