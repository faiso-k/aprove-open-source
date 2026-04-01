package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Search for POLOs by using a reduction to SAT and then applying a SAT solver.
 * Can also be used for solving a Diophantine Formula given a PoloSatConverter.
 *
 * Additionally uses partial MaxSAT to maximize the number of constraints to be
 * oriented strictly for searchstrict and, more generally, the number of
 * certain subformulae of a Diophantine Formula to be fulfilled.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class MaxSatSearch implements aprove.verification.oldframework.Algebra.Orders.Utility.POLO.MaxSearchAlgorithm {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.SatSearch.MaxSatSearch");

    public static long encodeTime;
    public static long solveTime;
    public static long decodeTime;

    private final boolean USE_DIO_FORMULAE = false;

    private MaxSATCheckerFactory maxSatCheckerFactory;
    private PoloSatConverter converter;

    //private volatile static int suffix = 1;

    private MaxSatSearch(MaxSATCheckerFactory factory, PoloSatConverter converter) {
        super();
        this.maxSatCheckerFactory = factory;
        this.converter = converter;
    }

    public static MaxSatSearch create(MaxSATCheckerFactory factory, PoloSatConverter converter) {
        return new MaxSatSearch(factory, converter);
    }

    @Override
    public Map<String, BigInteger> search(
            Set<SimplePolyConstraint> constraints,
            Set<SimplePolyConstraint> searchStrictConstraints, Abortion aborter)
                throws AbortionException {
        return this.search(constraints, searchStrictConstraints, null, aborter);
    }

    // TODO adapt to Max
    @Override
    public Map<String, BigInteger> search(Set<SimplePolyConstraint> constraints,
            Set<SimplePolyConstraint> searchStrictConstraints,
            SimplePolynomial maximizeMe, Abortion aborter) throws AbortionException {

        if (MaxSatSearch.log.isLoggable(Level.FINER)) {
            MaxSatSearch.log.log(Level.FINER, "Entered MaxSatSearch\n");
        }

        Map<String, BigInteger> result;

        Pair<Formula<None>, Map<String, PolyCircuit>> conversionResult;
        long l1, l2; // nanoseconds
        l1 = System.nanoTime();
        if (this.USE_DIO_FORMULAE) {
            FormulaFactory<Diophantine> dioFactory;
            dioFactory = new FullSharingFactory<Diophantine>();
            List<Formula<Diophantine>> conjuncts = new ArrayList<Formula<Diophantine>>();
            for (SimplePolyConstraint spc : constraints) {
                Diophantine dio = Diophantine.create(spc);
                Formula<Diophantine> f = dioFactory.buildTheoryAtom(dio);
                conjuncts.add(f);
            }

            if (! searchStrictConstraints.isEmpty()) {
                // TODO respect neqSearchstrict setting
                List<Formula<Diophantine>> searchStrictEqAtoms;
                searchStrictEqAtoms = new ArrayList<Formula<Diophantine>>(searchStrictConstraints.size());
                for (SimplePolyConstraint spc : searchStrictConstraints) {
                    SimplePolynomial lhsMinusRhs = spc.getPolynomial();
                    Pair<SimplePolynomial, SimplePolynomial> lhsAndRhs;
                    lhsAndRhs = lhsMinusRhs.toPositivePair();

                    Diophantine eqProposition = Diophantine.create(lhsAndRhs.x,
                            lhsAndRhs.y, ConstraintType.EQ);
                    Formula<Diophantine> fEq = dioFactory.buildTheoryAtom(eqProposition);
                    searchStrictEqAtoms.add(fEq);

                    Diophantine geProposition = Diophantine.create(lhsAndRhs.x,
                            lhsAndRhs.y, ConstraintType.GE);
                    Formula<Diophantine> fGe = dioFactory.buildTheoryAtom(geProposition);
                    conjuncts.add(fGe);
                }
                Formula<Diophantine> allEqual = dioFactory.buildAnd(searchStrictEqAtoms);
                Formula<Diophantine> notAllEqual = dioFactory.buildNot(allEqual);
                conjuncts.add(notAllEqual);
            }
            Formula<Diophantine> diophantineFormula = dioFactory.buildAnd(conjuncts);
            result = this.search(diophantineFormula, aborter);
            if (result == null) {
                return result;
            }
            // Is result really a solution for the given constraints?
            if (Globals.useAssertions) {
                for (SimplePolyConstraint constraint : constraints) {
                    assert constraint.interpret(result, BigInteger.ZERO);
                    // Using 0 as default value should be okay unless we forbid 0
                    // as possible value for some unassigned indefinite
                }
            }
        }
        else { // legacy stuff, we do not use Formula<Diophantine> here
            conversionResult = this.converter.convert(constraints, searchStrictConstraints, aborter);

            l2 = System.nanoTime();
            MaxSatSearch.encodeTime = l2 - l1;
            if (MaxSatSearch.log.isLoggable(Level.FINER)) {
                MaxSatSearch.log.log(Level.FINER, "Conversion of SimplePolyConstraints to SAT took {0} ms.\n",
                        (l2-l1)/1000000);
                MaxSatSearch.log.log(Level.FINER, "Indefinites to PolyCircuits: {0}\n", conversionResult.y);
            }

            /*
            if (false) { // testing the export to a file
                String dimacsString;
                dimacsString = FormulaToDimacsConverter.convert(conversionResult.x);
                try {
                    PrintWriter writer = new PrintWriter("/home/fuhs/dimacs/cnf"+(suffix++)+".dimacs");
                    writer.print(dimacsString);
                    writer.flush();
                    writer.close();
                }
                catch (FileNotFoundException e1) {
                    e1.printStackTrace();
                    throw new RuntimeException("File could not be accessed!");
                }
            }
            */

            aborter.checkAbortion();
            l1 = System.nanoTime();
            SATChecker satChecker = this.maxSatCheckerFactory.getSATChecker();
            /* TODO
             * Please check how to deal with a fail here
             *
             * -- thetux
             */
            int[] model;
            try {
                model = satChecker.solve(conversionResult.x, aborter);
            } catch (SolverException e) {
                model = null;
            }
            l2 = System.nanoTime();
            MaxSatSearch.solveTime = l2 - l1;
            if (model == null) {
                MaxSatSearch.decodeTime = 0;
                return null;
            }

            l1 = System.nanoTime();
            // get the logical interpretation
            Set<Integer> interpretation;
            // x \in interpretation <=> x |-> true

            interpretation = new HashSet<Integer>(model.length);
            for (int i = 0; i < model.length; ++i) {
                if (model[i] > 0) {
                    interpretation.add(model[i]);
                }
            }

            result = new LinkedHashMap<String, BigInteger>(conversionResult.y.size());
            IndefiniteBinarizer<String> bin = IndefiniteBinarizer.create(this.converter.getPropFactory(), this.converter.getConfig());
            for (Map.Entry<String, PolyCircuit> e : conversionResult.y.entrySet()) {
                PolyCircuit pc = e.getValue();
                List<Formula<None>> formulae = pc.getFormulae();

                BigInteger coeffValue = bin.natBig(formulae, interpretation);
                if (Globals.useAssertions) {
                    if (this.converter.getTracking()) {
                        assert coeffValue.compareTo(pc.getMax()) <= 0;
                    }
                }
                result.put(e.getKey(), coeffValue);
                if (MaxSatSearch.log.isLoggable(Level.FINEST)) {
                    MaxSatSearch.log.log(Level.FINEST, "{0} ", e);
                }
            }
            l2 = System.nanoTime();
            MaxSatSearch.decodeTime = l2 - l1;
            if (MaxSatSearch.log.isLoggable(Level.FINEST)) {
                MaxSatSearch.log.log(Level.FINEST, "\n");
            }

            // Is result really a solution for the given constraints?
            if (Globals.useAssertions) {
                for (SimplePolyConstraint constraint : constraints) {
                    assert constraint.interpret(result, BigInteger.ZERO);
                    // Using 0 as default value should be okay unless we forbid 0
                    // as possible value for some unassigned indefinite
                }
            }
        }

        if (MaxSatSearch.log.isLoggable(Level.FINER)) {
            MaxSatSearch.log.finer("Diophantine solution: " +
                    new TreeMap<String, BigInteger>(result) + "\n");
        }
        ////System.err.println(result);
        return result;
    }

    @Override
    public Map<String, BigInteger> search(Formula<Diophantine> f,
            Abortion aborter)
            throws AbortionException {
        return this.search(f, aborter, new LinkedHashSet<Formula<Diophantine>>());
    }


    /**
     * Searches for a solution of <code>f</code> using <code>converter</code>.
     *
     * @param f - a Diophantine formula for which a solution is supposed to be
     *  found
     * @param converter - the PoloSatConverter to be used for the conversion
     *  to SAT that is performed for the sake of the search
     * @param aborter - the Abortion to be used
     * @return a mapping from Diophantine unknowns to integers over the range
     *  specified inside the PoloSatConverter that satisfies f if such a
     *  mapping exists, otherwise: null
     * @throws AbortionException
     */
    public Map<String, BigInteger> search(Formula<Diophantine> f,
            Abortion aborter, Set<? extends Formula<Diophantine>> propVars)
            throws AbortionException {
        long l1, l2;
        l1 = System.nanoTime();
        Triple<Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> conversionResult;
        conversionResult = this.converter.convert(f, aborter);
        l2 = System.nanoTime();
        MaxSatSearch.encodeTime = l2 - l1;
        if (MaxSatSearch.log.isLoggable(Level.FINER)) {
            MaxSatSearch.log.log(Level.FINER, "Conversion of SimplePolyConstraints to SAT took {0} ms.\n",
                    (l2-l1)/1000000);
        }
        ////System.out.println("Time (ms) for constraints to Prop Logic: " + (l2-l1)/1000000);
        aborter.checkAbortion();
        SATChecker satChecker = this.maxSatCheckerFactory.getSATChecker();
        l1 = System.nanoTime();
        /* TODO
         * Please check how to deal with a fail here
         *
         * -- thetux
         */
        int[] model;
        try {
            model = satChecker.solve(conversionResult.x, aborter);
        } catch (SolverException e) {
            model = null;
        }
        l2 = System.nanoTime();
        //System.out.println("Time (ms) for Prop Logic to Dio model:   " + (l2-l1)/1000000);
        MaxSatSearch.solveTime = l2 - l1;
        if (model == null) {
            MaxSatSearch.decodeTime = 0;
            return null;
        }

        l1 = System.nanoTime();
        // get the logical interpretation
        Set<Integer> interpretation;
        // x \in interpretation <=> x |-> true

        interpretation = new HashSet<Integer>(model.length);
        for (int i = 0; i < model.length; ++i) {
            if (model[i] > 0) {
                interpretation.add(model[i]);
            }
        }

        Iterator<? extends Formula<Diophantine>> iter = propVars.iterator();
        while (iter.hasNext()) {
            Formula<Diophantine> v = iter.next();
            if (!interpretation.contains(conversionResult.z.get(v).getId())) {
                iter.remove();
            }
        }


        if (MaxSatSearch.log.isLoggable(Level.FINEST)) {
            MaxSatSearch.log.log(Level.FINEST, "MaxSatSearch found the solution:\n");
        }

        Map<String, BigInteger> result;
        result = new LinkedHashMap<String, BigInteger>(conversionResult.y.size());
        IndefiniteBinarizer<String> bin = IndefiniteBinarizer.create(this.converter.getPropFactory(), this.converter.getConfig());
        for (Map.Entry<String, PolyCircuit> e : conversionResult.y.entrySet()) {
            PolyCircuit pc = e.getValue();
            List<Formula<None>> formulae = pc.getFormulae();
            BigInteger coeffValue = bin.natBig(formulae, interpretation);
            if (Globals.useAssertions) {
                if (this.converter.getTracking()) {
                    assert coeffValue.compareTo(pc.getMax()) <= 0;
                }
            }
            result.put(e.getKey(), coeffValue);
            if (MaxSatSearch.log.isLoggable(Level.FINEST)) {
                MaxSatSearch.log.log(Level.FINEST, e.getKey() + "=" + coeffValue + " ");
            }
        }
        ////System.out.println(result);
        if (MaxSatSearch.log.isLoggable(Level.FINEST)) {
            MaxSatSearch.log.log(Level.FINEST, "\n");
        }
        l2 = System.nanoTime();
        MaxSatSearch.decodeTime = l2 - l1;
        return result;
    }


    @Override
    public Map<String, BigInteger> searchMax(Formula<Diophantine> f,
            Collection<Formula<Diophantine>> maxThem, Abortion aborter) throws AbortionException {
        long l1, l2;
        l1 = System.nanoTime();
        Quadruple<Map<Formula<Diophantine>, Formula<None>>, Formula<None>,
            Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> conversionResult;
        conversionResult = this.converter.convert(f, maxThem, aborter);
        l2 = System.nanoTime();
        MaxSatSearch.encodeTime = l2 - l1;
        if (MaxSatSearch.log.isLoggable(Level.FINER)) {
            MaxSatSearch.log.log(Level.FINER, "Conversion of SimplePolyConstraints to SAT took {0} ms.\n",
                    (l2-l1)/1000000);
        }
        ////System.out.println("Time (ms) for constraints to Prop Logic: " + (l2-l1)/1000000);
        aborter.checkAbortion();
        MaxSATChecker satChecker = this.maxSatCheckerFactory.getMaxSATChecker();
        l1 = System.nanoTime();
        final int[] model = satChecker.solve(conversionResult.x, conversionResult.w.values(), aborter);
        l2 = System.nanoTime();
        //System.out.println("Time (ms) for Prop Logic to Dio model:   " + (l2-l1)/1000000);
        MaxSatSearch.solveTime = l2 - l1;
        if (model == null) {
            MaxSatSearch.decodeTime = 0;
            return null;
        }

        l1 = System.nanoTime();
        // get the logical interpretation
        Set<Integer> interpretation;
        // x \in interpretation <=> x |-> true

        interpretation = new HashSet<Integer>(model.length);
        for (int i = 0; i < model.length; ++i) {
            if (model[i] > 0) {
                interpretation.add(model[i]);
            }
        }

        if (MaxSatSearch.log.isLoggable(Level.FINEST)) {
            MaxSatSearch.log.log(Level.FINEST, "MaxSatSearch found the solution:\n");
        }

        Map<String, BigInteger> result;
        result = new LinkedHashMap<String, BigInteger>(conversionResult.y.size());
        IndefiniteBinarizer<String> bin = IndefiniteBinarizer.create(this.converter.getPropFactory(), this.converter.getConfig());
        for (Map.Entry<String, PolyCircuit> e : conversionResult.y.entrySet()) {
            PolyCircuit pc = e.getValue();
            List<Formula<None>> formulae = pc.getFormulae();
            BigInteger coeffValue = bin.natBig(formulae, interpretation);
            if (Globals.useAssertions) {
                if (this.converter.getTracking()) {
                    assert coeffValue.compareTo(pc.getMax()) <= 0;
                }
            }
            result.put(e.getKey(), coeffValue);
            if (MaxSatSearch.log.isLoggable(Level.FINEST)) {
                MaxSatSearch.log.log(Level.FINEST, e.getKey() + "=" + coeffValue + " ");
            }
        }
        ////System.out.println(result);
        if (MaxSatSearch.log.isLoggable(Level.FINEST)) {
            MaxSatSearch.log.log(Level.FINEST, "\n");
        }
        l2 = System.nanoTime();
        MaxSatSearch.decodeTime = l2 - l1;
        return result;
    }


    public boolean supportsSpecialRanges() {
        return true;
    }

    @Override
    public BigInteger getRange(String a) {
        return this.converter.getRange(a);
    }

    @Override
    public DefaultValueMap<String, BigInteger> getRanges() {
        return this.converter.getRanges();
    }

    @Override
    public void putRange(String a, BigInteger newRange) {
        this.converter.putRange(a, newRange);
    }

    @Override
    public boolean supportsDL() {
        return true;
    }

    @Override
    public FormulaFactory<Diophantine> getDLFactory() {
        return this.converter.getDioFactory();
    }

    public PoloSatConverter getConverter() {
        return this.converter;
    }

    @Override
    public boolean introducesFreshVariables() {
        return false;
    }

	@Override
	public Map<String, BigInteger> searchLRA(Formula<Diophantine> fml, Abortion aborter) throws AbortionException {
		
		return null;
	}
}
