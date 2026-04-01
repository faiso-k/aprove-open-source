package aprove.solver.Engines;

import java.math.*;
import java.util.*;

import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.SMTSearch.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.SMTUtility.*;

public abstract class SMTEngine extends Engine {
    /** The format of the string passed to the actual engine. */
    private final Splitter splitter;

    private final BeforeSplitter bSplitter;

    private final Domain domain;

    private final boolean valueMapOptimizer;

    private final boolean splitBeforeVisit;

    /** Logics supported by our solvers. */
    public static enum SMTLogic {
        /** Quantifier-free bit vector operations. */
        QF_BV,

        /** Quantifier-free linear integer arithmetic. */
        QF_LIA,

        /** Quantifier-free non-linear integer arithmetic. */
        QF_NIA,

        /** Quantifier-free linear real arithmetic. */
        QF_LRA,
        
        /** Quantifier-free non-linear real arithmetic. */
        QF_NRA,

        /** Quantifier-free real arithmetic. (does not exists?) */
        QF_RA;

        public String getName() {
            return this.toString();
        }
    }

    public static enum Splitter {
        HIGHEST_EXP, MOST_OFTEN, LEAST_OFTEN, MINIMAL_SET
    }

    public static enum BeforeSplitter {
        MIN_SET, MO_IGNORE_EXPONENT, MO_RESPECT_EXPONENT, DO_NOT
    }

    @ParamsViaArgumentObject
    public SMTEngine(final Arguments arguments) {
//        throw new RuntimeException();
//        System.exit(24);
        this.splitter = arguments.splitter;
        this.domain = arguments.domain;
        this.valueMapOptimizer = arguments.valueMapOptimizer;
        this.splitBeforeVisit = arguments.splitBeforeVisit;
        this.bSplitter = arguments.bSplitter;
    }

    /**
     * Call the engine on a problem given as a list of formulas and return
     * result. If the formula has a satisfying assignment, the model is stored
     * in the formula.
     * @param formulas list of formulas to solve
     * @param logic the used logics in the formulas.
     * @param aborter is checked for abortions.
     * @return YES for SAT, NO for UNSAT, MAYBE for UNKNOWN
     * @throws AbortionException when we were asked to abort.
     * @throws WrongLogicException when the formula does not match the logic
     * (and the solver complains)
     */
    public abstract YNM satisfiable(List<Formula<SMTLIBTheoryAtom>> formulas, SMTLogic logic, Abortion aborter)
            throws AbortionException, WrongLogicException;

    /**
     * Call the engine on a problem given as a list of formulas and return
     * result and model (if one exists). Does not touch the formula.
     * @param formulas list of formulas to solve
     * @param logic the used logics in the formulas.
     * @param aborter is checked for abortions.
     * @return pair of a YNM (YES for SAT, NO for UNSAT, MAYBE for UNKNOWN) and
     * a model, which is only valid if the formula was satisfiable.
     * @throws AbortionException when we were asked to abort.
     * @throws WrongLogicException when the formula does not match the logic
     * (and the solver complains)
     */
    public abstract Pair<YNM, Map<String, String>> solve(List<Formula<SMTLIBTheoryAtom>> formulas,
        SMTLogic logic,
        Abortion aborter) throws AbortionException, WrongLogicException;

    /**
     * Call the engine on a problem given as a string and return result and
     * model (if one exists). Does not touch the formula.
     * @param smtString the encoded problem.
     * @param logic the used logics in the formulas.
     * @param aborter is checked for abortions.
     * @return pair of a YNM (YES for SAT, NO for UNSAT, MAYBE for UNKNOWN) and
     * a model, which is only valid if the formula was satisfiable.
     * @throws AbortionException when we were asked to abort.
     * @throws WrongLogicException when the formula does not match the logic
     * (and the solver complains)
     */
    public abstract Pair<YNM, Map<String, String>> solve(String smtString, SMTLogic logic, Abortion aborter)
            throws AbortionException, WrongLogicException;

    /**
     * @param smtResultMap a Map from variable/function names to a string representation of their value
     * @param varNameMap a variable map created when encoding the SMTLIB problem to text
     * @return a modified smtResultMap in which the variable renamings performed when creating a text representation
     *  for the SMT solver have been reversed.
     */
    public static Map<String, String> translateResultMapToOldNames(final Map<String, String> smtResultMap,
        final SMTLIBVarNameMap varNameMap) {
        // Retrieve the old names and create a proper variable mapping:
        if (smtResultMap != null) {
            final Map<String, String> translatedResultMap = new LinkedHashMap<>();
            final Map<String, SMTLIBAssignableSemantics> nameToVarMap = varNameMap.getNameToVarMap();
            for (final Map.Entry<String, String> e : smtResultMap.entrySet()) {
                final String smtKey = e.getKey();
                final String val = e.getValue();

                if (smtKey.startsWith("(")) {
                    assert (false) : "Cannot translate function result";
                } else {
                    // Variable value
                    final SMTLIBVariable<?> v = (SMTLIBVariable<?>) nameToVarMap.get(smtKey);
                    if (v != null) {
                        translatedResultMap.put(v.getName(), val);
                    }
                }
            }
            return translatedResultMap;
        }
        return null;
    }

    @Override
    public SearchAlgorithm getSearchAlgorithm(final DefaultValueMap<String, BigInteger> ranges) {
        FormulaFactory<SMTLIBTheoryAtom> factory;
        factory = new FullSharingFactory<SMTLIBTheoryAtom>();

        // If the Domain is an Integer Interval we HAVE to use LIA,
        // if we would use Integer Intervals on LRA,... well that would not work out :)
        DioSMTConverter converter;
        if (this.domain != null) {
            converter = DioSMTConverter.create(factory, this.domain, this.splitter, this.valueMapOptimizer);
            converter.setValues(ranges);
        } else if (ranges != null) {
            converter = DioSMTConverter.create(factory, ranges, this.splitter, this.valueMapOptimizer);
        } else {
            throw new RuntimeException("Ranges is null, that does not work!");
        }
        return new SMTSearch(ranges, converter, this, this.splitBeforeVisit, this.bSplitter);
    }

    public static class Arguments {
        public Splitter splitter = Splitter.HIGHEST_EXP;

        public Domain domain = null;

        public boolean splitBeforeVisit = false;

        public boolean valueMapOptimizer = true;

        public BeforeSplitter bSplitter = BeforeSplitter.DO_NOT;
    }

}
