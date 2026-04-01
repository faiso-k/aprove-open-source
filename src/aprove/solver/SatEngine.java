package aprove.solver;

import java.math.*;

import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Common superclass for SatEngines.
 *
 * Furthermore, we can obtain a FormulaFactory that corresponds to the
 * config options as passed from the strategy. Like this, SatEngine also
 * works as a MetaFormulaFactory.
 *
 *
 * Note:
 * Orders.properties (config file for the Engines) contains the following line:
 * Engine = aprove.solver.Engine
 *
 * @author Carsten Fuhs
 */
public abstract class SatEngine extends Engine {

    // simplify Boolean expressions? (e.g., 1 and X becomes X)
    // in most circumstances, the default "True" is what you want.
    // exists for showing why simplifying is a good idea.
    // currently only has an effect if Sharing = True and
    // NodeLimit <= 0.
    private final boolean simplify;

    // do we share common subformulae?
    private final boolean sharing;

    // what way are n-ary OrFormulae to be constructed?
    private final SplitMode orMode;

    // what way are n-ary AndFormulae to be constructed?
    private final SplitMode andMode;

    // max number of nodes in the Boolean tree/DAG; <= 0 means no limit
    private final int nodeLimit;

    // use xor clauses? (should default to false for now)
    protected final boolean xorClauses;

    public SatEngine(Arguments arguments) {
        this.andMode = arguments.andMode;
        this.nodeLimit = arguments.nodeLimit;
        this.orMode = arguments.orMode;
        this.sharing = arguments.sharing;
        this.simplify = arguments.simplify;
        this.xorClauses = arguments.xorClauses;
    }

    /**
     * @return a FormulaFactory that corresponds to the attributes of this.
     */
    public FormulaFactory<None> getFormulaFactory() {
        if (this.sharing) {
            if (this.nodeLimit > 0) {
                return CountingCircuitFactory.create(this.andMode, this.orMode, this.nodeLimit);
            }
            else {
                if (this.simplify) {
                    return NonCountingCircuitFactory.create(this.andMode, this.orMode);
                }
                else {
                    return ListSharingFactory.create();
                }
            }
        }
        else {
            if (this.nodeLimit > 0) {
                return aprove.verification.oldframework.PropositionalLogic.Formulae.CountingFormulaFactory.create(this.andMode, this.orMode, this.nodeLimit);
            }
            else {
                if (this.simplify) {
                    return NonCountingFormulaFactory.create(this.andMode, this.orMode);
                }
                else {
                    return new AtomCachingFactory<None>();
                }
            }
        }
    }

    /**
     * This method is to be implemented by SatEngines!
     *
     * @return a corresponding SATChecker
     */
    @Override
    public abstract SATChecker getSATChecker();

    @Override
    public SearchAlgorithm getSearchAlgorithm(DefaultValueMap<String, BigInteger> ranges) {
        throw new UnsupportedOperationException("Sorry, additionally a DiophantineSATConverter is needed.");
    }

    public SearchAlgorithm getSearchAlgorithm(DefaultValueMap<String, BigInteger> ranges, DiophantineSATConverter satConverter) {
        FormulaFactory<None> propFactory = this.getFormulaFactory();
        PoloSatConverter poloSatConverter = satConverter.getPoloSatConverter(propFactory,
                ranges, ranges.getDefaultValue());
        SearchAlgorithm searchAlg = SatSearch.create(this, poloSatConverter);
        return searchAlg;
    }

    @Override
    public boolean supportsDL() {
        return true;
    }

    public static class Arguments {
        public SplitMode andMode = SplitMode.FLATTEN;
        public int nodeLimit = -1;
        public SplitMode orMode = SplitMode.FLATTEN;
        public boolean sharing = true;
        public boolean simplify = true;
        public boolean xorClauses = false;
    }

}