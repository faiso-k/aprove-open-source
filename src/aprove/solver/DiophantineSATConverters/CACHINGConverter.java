package aprove.solver.DiophantineSATConverters;

import java.math.*;
import java.util.*;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Conversion from Diophantine problems to SAT problems
 * that caches the formula tuples (circuits) that
 * correspond to some arithmetic expressions.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class CACHINGConverter extends DiophantineSATConverter {

    @ParamsViaArgumentObject
    public CACHINGConverter(Arguments arguments) {
        super(arguments);
    }

    @Override
    public PoloSatConverter getPoloSatConverter(FormulaFactory<None> factory, Map<String, BigInteger> ranges, BigInteger defaultRange) {
        return CachingSPCToCircuitConverter.create(factory, ranges, defaultRange,
                this.getPoloSatConfigInfo());
    }
}
