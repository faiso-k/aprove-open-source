package aprove.solver.Engines;

import java.math.*;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class MiniMaxSATEngine extends SatEngine implements MaxSATCheckerFactory {

    @ParamsViaArgumentObject
    public MiniMaxSATEngine(Arguments arguments) {
        super(arguments);
    }

    @Override
    public MaxSATChecker getMaxSATChecker() {
        return new MiniMaxSATFileChecker();
    }

    @Override
    public SATChecker getSATChecker() {
        return this.getMaxSATChecker();
    }

    @Override
    public MaxSearchAlgorithm getSearchAlgorithm(DefaultValueMap<String, BigInteger> ranges, DiophantineSATConverter satConverter) {
        FormulaFactory<None> propFactory = this.getFormulaFactory();
        PoloSatConverter poloSatConverter = satConverter.getPoloSatConverter(propFactory,
                ranges, ranges.getDefaultValue());
        MaxSearchAlgorithm searchAlg = MaxSatSearch.create(this, poloSatConverter);
        return searchAlg;
    }
}
