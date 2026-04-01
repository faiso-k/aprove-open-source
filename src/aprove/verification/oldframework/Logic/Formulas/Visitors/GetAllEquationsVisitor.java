package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * This method should return a list of equations containted in the specified formula
* @author Eugen
*/
public class GetAllEquationsVisitor implements CoarseFormulaVisitor{

    protected  Vector<Equation> res ;

    //Constructor
    protected GetAllEquationsVisitor(){
          this.res =  new Vector<Equation>();
    }

    public static List<Equation> applyTo(Formula f){
        GetAllEquationsVisitor vis  = new GetAllEquationsVisitor();
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
        this.res.add(eqFormula);
        return null;
    }

    @Override
    public Object caseJunctorFormula( JunctorFormula jFormula ){
        if (jFormula.getLeft()!=null) {
            jFormula.getLeft().apply(this);
        }
        if (jFormula.getRight()!=null) {
            jFormula.getRight().apply(this);
        }
        return null;
    }
}

