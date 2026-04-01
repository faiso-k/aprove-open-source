package aprove.verification.oldframework.Logic.Formulas.Visitors ;


import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;

/** returns all variables in a formula. use the "apply" method
 *  of this class.
 * Note: This method is potentially unsafe, since the vars are reference to part of the fomrula
 * @author  Burak, eugen
 * @version $Id$
 */

public class GetAllVariablesVisitor implements CoarseFormulaVisitor
{

    @Override
    public Object caseTruthValue(  FormulaTruthValue truthvalFormula ) {
    return new LinkedHashSet<AlgebraVariable>();
    }

    // getVars() for terms is potentially unsafe as well
    @Override
    public Object caseEquation( Equation eqFormula  ) {
        AlgebraTerm s = eqFormula.getLeft();
        AlgebraTerm t = eqFormula.getRight();
    Set<AlgebraVariable> a = s.getVars();
    Set<AlgebraVariable> b = t.getVars();
        a.addAll( b );
    return a;
    }

    @Override
    public Object caseJunctorFormula(  JunctorFormula jFormula ) {
        Formula phi = jFormula.getLeft();
        Formula psi = jFormula.getRight();
    Set<AlgebraVariable> a = (Set<AlgebraVariable>) phi.apply( this );
    if( psi != null) {
        Set<AlgebraVariable> b = (Set<AlgebraVariable>) psi.apply( this );
        a.addAll( b );
    }
    return a;
    }

    public static Set<AlgebraVariable> apply( Formula phi ) {
    GetAllVariablesVisitor v = new GetAllVariablesVisitor();
    return (Set<AlgebraVariable>) phi.apply( v );
    }
}
