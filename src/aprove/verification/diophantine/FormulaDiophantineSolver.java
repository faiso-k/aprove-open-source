package aprove.verification.diophantine;

import static aprove.verification.diophantine.InfInt.InfIntType.*;

import java.io.*;
import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import org.antlr.runtime.*;

import aprove.*;
import aprove.input.Generated.SMTLIB.*;
import aprove.input.Programs.SMTLIB.*;
import aprove.strategies.Abortions.*;
import aprove.verification.diophantine.GlobalConstraintAnalyzers.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class FormulaDiophantineSolver {

    private enum GlobalAnalyzer {
        DIRECT, TRIVIAL;
    }

    private static final GlobalAnalyzer ANALYZER = GlobalAnalyzer.DIRECT;

    public static Map<String, BigInteger> solve(
        final Reader input,
        final String stratString,
        final BigInteger range,
        final boolean verbose,
        final Abortion aborter) throws AbortionException
    {

        final SMTBenchmark benchmark = FormulaDiophantineSolver.parse(input);
        if (benchmark == null) {
            // Parse error
            return null;
        }

        if (verbose) {
            System.err.println("+FORMULA: " + benchmark.getAssertions());
            System.err.println("+STATUS: " + benchmark.getStatus());
        }

        if (!benchmark.doCheckSat()) {
            throw new IllegalArgumentException("(check-sat) not set");
        }
        if (range.signum() <= 0) {
            throw new IllegalArgumentException("Range " + range + " not allowed, must be positive!");
        }

        BigInteger lowerDefault = range.negate().add(BigInteger.ONE);
        BigInteger upperDefault = range;

        final Formula<Diophantine> originalFormula = benchmark.getAssertions();

        // now deduce ranges via incredibly sophisticated heuristics
        GlobalConstraintAnalyzer analyzer;
        switch (FormulaDiophantineSolver.ANALYZER) {
        case TRIVIAL:
            analyzer = new TrivialGlobalAnalyzer();
            break;
        case DIRECT:
            analyzer = new DirectGlobalAnalyzer();
            break;
        default:
            throw new IllegalStateException("Did not find suitable analyzer type!");
        }
        final DefaultValueMap<String, SearchBounds> globalRangeConstraints = analyzer.analyze(originalFormula);

        // rangeHeuristic.computeRanges(originalFormula);
        // boolean complete = rangeHeuristic.wasComplete();

        DefaultValueMap<String, BigInteger> searchRange = null;

        // if the solver says that a = n for a variable a,
        // then n + addToResultOffsets(a) is the real solution for a
        // (offset needed because search algorithms only search over 0..k)
        DefaultValueMap<String, BigInteger> addToResultOffsets = null;

        Map<String, BigInteger> retMap = null;
        while (retMap == null) {
            if (Globals.useAssertions) {
                assert lowerDefault.compareTo(upperDefault) < 0;
            }
            if (verbose) {
                System.err.println("+CURRENT DEFAULT SEARCH RANGE: [" + lowerDefault + ", " + upperDefault + ']');
            }
            final Pair<DefaultValueMap<String, BigInteger>, DefaultValueMap<String, BigInteger>> searchRangeWithOffsets;
            searchRangeWithOffsets =
                FormulaDiophantineSolver.computeSearchRangeWithOffsets(
                    globalRangeConstraints,
                    lowerDefault,
                    upperDefault);
            searchRange = searchRangeWithOffsets.x;
            addToResultOffsets = searchRangeWithOffsets.y;

            final Formula<Diophantine> formula = FormulaDiophantineSolver.getFormula(benchmark, addToResultOffsets);

            final SearchAlgorithm searchAlg = EngineHack.getSearchAlg(stratString, searchRange, false);

            retMap = searchAlg.search(formula, aborter);
            if (retMap == null) {
                // TODO
                // Has our search by chance been complete?
                // This can be the case if the global constraints
                // tell us that every variable in the Formula<Diophantine>
                // has a finite range, which we have happened to cover.

                // recompute ranges for the next iteration
                final BigIntegerInterval newLowerUpperDefault =
                    FormulaDiophantineSolver.computeNewDefaultRanges(lowerDefault, upperDefault);
                lowerDefault = newLowerUpperDefault.min;
                upperDefault = newLowerUpperDefault.max;
            }
        }

        if (verbose) {
            System.err.println("+NON-NEGATIVE SEARCH RANGE: " + searchRange);
            System.err.println("+OFFSETS: " + addToResultOffsets);
        }

        // only output solutions for variables that occur in the input
        retMap.keySet().retainAll(benchmark.getVariables());

        // adjust solutions for offsets needed to search for negative numbers
        for (final Entry<String, BigInteger> e : retMap.entrySet()) {
            final String var = e.getKey();
            final BigInteger offsetAddend = addToResultOffsets.get(var);
            e.setValue(e.getValue().add(offsetAddend));
        }
        return retMap;
    }

    /**
     * Compute new upper and lower ranges for the search.
     * Could also be made configurable using dedicated classes for
     * different heuristics.
     *
     * @param oldLower
     * @param oldUpper
     * @return [oldLower - oldUpper, 2*oldUpper]
     */
    private static BigIntegerInterval computeNewDefaultRanges(final BigInteger oldLower, final BigInteger oldUpper) {
        final BigInteger newLower = oldLower.subtract(oldUpper);
        final BigInteger newUpper = oldUpper.shiftLeft(1);
        return new BigIntegerInterval(newLower, newUpper);
    }

    /**
     * @param globalConstraints - knowledge deduced from the input formula
     * @param lowerDefault - use as lower default value
     * @param upperDefault - use as upper default value
     * @return pair with<br>
     *  x: range to be used for the SearchAlgorithm<br>
     *  y: number to be added to the result of the SearchAlgorithm
     *     to make sense for the original problem (before that, a variable
     *     "a" shall need to be substituted by the polynomial "a - y(a)")
     */
    private static
        Pair<DefaultValueMap<String, BigInteger>, DefaultValueMap<String, BigInteger>>
        computeSearchRangeWithOffsets(
            final DefaultValueMap<String, SearchBounds> globalConstraints,
            final BigInteger lowerDefault,
            final BigInteger upperDefault)
    {
        // by default shift a var in [var / var + offsetAddend] by lowerDefault
        final BigInteger offsetAddendDefault = lowerDefault;
        final DefaultValueMap<String, BigInteger> offsetAddends =
            new DefaultValueMap<String, BigInteger>(offsetAddendDefault);

        // the SearchAlgorithm by default sees the difference between
        // upper and lower defaults
        final BigInteger totalDefault = upperDefault.subtract(lowerDefault);
        final DefaultValueMap<String, BigInteger> searchRange = new DefaultValueMap<String, BigInteger>(totalDefault);

        // for all the variables for which we have explicit knowledge
        // (for the others the defaults are fine) ...
        for (final Entry<String, SearchBounds> varToBounds : globalConstraints.entrySet()) {
            final String var = varToBounds.getKey();
            final SearchBounds bounds = varToBounds.getValue();
            final InfInt lowerBound = bounds.getLowerBound();
            final InfInt upperBound = bounds.getUpperBound();

            // By how much do we shift var in [var / var + offsetAddend]?
            // (note that offsetAddend is typically negative)
            final BigInteger offsetAddend;
            if (lowerBound.getType() == FINITE) {
                final BigInteger lowerBoundNumber = lowerBound.getNumber();
                offsetAddend = lowerBoundNumber.max(lowerDefault);
            } else { // no knowledge on var's lower bound
                offsetAddend = lowerDefault;
            }

            // Now figure out which range the SearchAlgorithm shall get to see.
            final BigInteger totalRange;
            if (upperBound.getType() == FINITE) {
                final BigInteger upperBoundNumber = upperBound.getNumber();
                totalRange = upperBoundNumber.min(upperDefault).subtract(offsetAddend).max(BigInteger.ONE); // do some search in any case;
            } else { // no knowledge on var's upper bound
                totalRange = upperDefault.subtract(offsetAddend).max(BigInteger.ONE); // do some search in any case
            }

            // Put this information into the corresponding maps.
            offsetAddends.put(var, offsetAddend);
            searchRange.put(var, totalRange);
        }
        return new Pair<DefaultValueMap<String, BigInteger>, DefaultValueMap<String, BigInteger>>(
            searchRange,
            offsetAddends);
    }

    /**
     * @param benchmark
     * @param offsetAddends e.g. [var -> n] where n is typically negative
     *  to denote that we want to get a formula that allows to search
     *  for solutions for var starting from n
     * @return
     */
    private static Formula<Diophantine> getFormula(
        final SMTBenchmark benchmark,
        final DefaultValueMap<String, BigInteger> offsetAddends)
    {
        final Map<String, SimplePolynomial> substitution =
            FormulaDiophantineSolver.getSubstitution(benchmark, offsetAddends);
        final FormulaFactory<Diophantine> factory = new FullSharingFlatteningFactory<Diophantine>();
        final DiophantineSubstitutor converter = new DiophantineSubstitutor(substitution, factory);
        final TheoryConverterVisitor<Diophantine, Diophantine> visitor =
            new TheoryConverterVisitor<Diophantine, Diophantine>(
                factory,
                converter,
                new LinkedHashMap<Variable<Diophantine>, Variable<Diophantine>>());

        return benchmark.getAssertions().apply(visitor);
    }

    /**
     * @param benchmark
     * @param offsetAddends contains e.g. [a -> n]
     *  (n is typically negative)
     * @return map with e.g. [a -> a + n]
     */
    private static Map<String, SimplePolynomial> getSubstitution(
        final SMTBenchmark benchmark,
        final DefaultValueMap<String, BigInteger> offsetAddends)
    {
        final Map<String, SimplePolynomial> substitution = new LinkedHashMap<String, SimplePolynomial>();

        for (final String s : benchmark.getVariables()) {
            final BigInteger range = offsetAddends.get(s);
            substitution.put(s, SimplePolynomial.create(s).plus(SimplePolynomial.create(range)));
        }
        for (final String s : benchmark.getLetVariables()) {
            final BigInteger range = offsetAddends.get(s);
            substitution.put(s, SimplePolynomial.create(s).plus(SimplePolynomial.create(range)));
        }

        return substitution;
    }

    private static SMTBenchmark parse(final Reader input) {
        SMTBenchmark benchmark;
        try {
            final SMTBenchmarkLexer lex = new SMTBenchmarkLexer(new ANTLRReaderStream(input));
            final CommonTokenStream tokens = new CommonTokenStream(lex);
            final SMTBenchmarkParser parser = new SMTBenchmarkParser(tokens);

            benchmark = parser.script();
        } catch (final IOException e) {
            System.err.println(e.toString());
            System.err.println("ERROR: Could not open input file; aborting\n-");
            benchmark = null;
        } catch (final RecognitionException e) {
            System.err.println(e.toString());
            System.err.println("ERROR: Could not parse input file; aborting\n-");
            benchmark = null;
        } catch (final Exception e) {
            e.printStackTrace();
            System.err.println("ERROR: Unknown exception trying to parse input file; aborting\n-");
            benchmark = null;
        }
        return benchmark;
    }
}
