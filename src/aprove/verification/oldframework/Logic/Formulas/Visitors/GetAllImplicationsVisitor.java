package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Logic.Formulas.*;



/**
 * This method should return a list of implications containted in the specified formula
* @author Eugen
*/
public class GetAllImplicationsVisitor implements CoarseFormulaVisitor{

    protected  Set<Formula> res ;

    //Constructor
    protected GetAllImplicationsVisitor(){
          this.res =  new HashSet<Formula>();
    }

    public static Set<Formula> applyTo(Formula f){
        GetAllImplicationsVisitor vis  = new GetAllImplicationsVisitor();
        f.apply(vis);
        return vis.res;
    }




    //4 different cases
    //we can assume that currentpos is initialized by "iterate()"
    @Override
    public Object caseTruthValue( FormulaTruthValue truthvalFormula ){
        return null;
    }

    @Override
    public Object caseEquation(Equation eqFormula ){
        return null;
    }

    @Override
    public Object caseJunctorFormula( JunctorFormula jFormula ){
        if (jFormula instanceof Implication) {
            this.res.add(jFormula);
        }
        if (jFormula.getLeft()!=null) {
            jFormula.getLeft().apply(this);
        }
        if (jFormula.getRight()!=null) {
            jFormula.getRight().apply(this);
        }
        return null;
    }
}

