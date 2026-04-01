package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import org.sat4j.specs.*;
import org.sat4j.tools.*;

import aprove.*;
import aprove.solver.Engines.*;
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
 * @author Carsten Fuhs
 * @version $Id$
 */
public class SatSearch implements aprove.verification.oldframework.Algebra.Orders.Utility.POLO.SearchAlgorithm {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.SatSearch.SatSearch");

    public static long encodeTime;
    public static long solveTime;
    public static long decodeTime;

    private final boolean USE_DIO_FORMULAE = false;

    private SATCheckerFactory satCheckerFactory;
    private PoloSatConverter converter;

    //private volatile static int suffix = 1;

    private SatSearch(SATCheckerFactory factory, PoloSatConverter converter) {
        super();
        this.satCheckerFactory = factory;
        this.converter = converter;
    }

    public static SatSearch create(SATCheckerFactory factory, PoloSatConverter converter) {
        return new SatSearch(factory, converter);
    }

    @Override
    public Map<String, BigInteger> search(
            Set<SimplePolyConstraint> constraints,
            Set<SimplePolyConstraint> searchStrictConstraints, Abortion aborter)
                throws AbortionException {
        return this.search(constraints, searchStrictConstraints, null, aborter);
    }

    @Override
    public Map<String, BigInteger> search(Set<SimplePolyConstraint> constraints,
            Set<SimplePolyConstraint> searchStrictConstraints,
            SimplePolynomial maximizeMe, Abortion aborter) throws AbortionException {

        if (SatSearch.log.isLoggable(Level.FINER)) {
            SatSearch.log.log(Level.FINER, "Entered SatSearch\n");
        }

        // TODO make the search range not just [0..n], but [n_i..n_j]*,
        // e.g., [0,1,2,10] might be interesting; this might be accomplished
        // by introducing new formulae that encode that bin(a) encodes
        // 0 or 1 or 2 or 10 because contrary to SimplePolyConstraints,
        // disjunctions are quite possible in formulae.

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
            aborter.checkAbortion();
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
            SatSearch.encodeTime = l2 - l1;
            if (SatSearch.log.isLoggable(Level.FINER)) {
                SatSearch.log.log(Level.FINER, "Conversion of SimplePolyConstraints to SAT took {0} ms.\n",
                        (l2-l1)/1000000);
                SatSearch.log.log(Level.FINER, "Indefinites to PolyCircuits: {0}\n", conversionResult.y);
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
            SATChecker satChecker = this.satCheckerFactory.getSATChecker();
            int[] model;
            try {
                model = satChecker.solve(conversionResult.x, aborter);
            } catch (SolverException e) {
                model = null;
            }
            l2 = System.nanoTime();
            SatSearch.solveTime = l2 - l1;
            if (model == null) {
                SatSearch.decodeTime = 0;
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
            IndefiniteConverter<String> bin = this.converter.getBinarizer();
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
                if (SatSearch.log.isLoggable(Level.FINEST)) {
                    SatSearch.log.log(Level.FINEST, "{0} ", e);
                }
            }
            l2 = System.nanoTime();
            SatSearch.decodeTime = l2 - l1;
            if (SatSearch.log.isLoggable(Level.FINEST)) {
                SatSearch.log.log(Level.FINEST, "\n");
            }

            // Is result really a solution for the given constraints?
            if (Globals.useAssertions) {
                for (SimplePolyConstraint constraint : constraints) {
                    assert constraint.interpret(result, BigInteger.ZERO) :
                        constraint + ", " + new TreeMap<String, BigInteger>(result);
                    // Using 0 as default value should be okay unless we forbid 0
                    // as possible value for some unassigned indefinite
                }
            }
        }

        if (SatSearch.log.isLoggable(Level.FINER)) {
            SatSearch.log.finer("Diophantine solution: " +
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
    public Map<String, BigInteger> search(final Formula<Diophantine> f,
            final Abortion aborter, final Set<? extends Formula<Diophantine>> propVars)
            throws AbortionException {
        aborter.checkAbortion();
        long l1, l2;
        l1 = System.nanoTime();
        Triple<Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> conversionResult;
        conversionResult = this.converter.convert(f, aborter);
        l2 = System.nanoTime();
        SatSearch.encodeTime = l2 - l1;
        if (SatSearch.log.isLoggable(Level.FINER)) {
            SatSearch.log.log(Level.FINER, "Conversion of SimplePolyConstraints to SAT took {0} ms.\n",
                    (l2-l1)/1000000);
        }
        ////System.out.println("Time (ms) for constraints to Prop Logic: " + (l2-l1)/1000000);
        aborter.checkAbortion();
        SATChecker satChecker = this.satCheckerFactory.getSATChecker();
        l1 = System.nanoTime();
        int[] model;
        try {
            model = satChecker.solve(conversionResult.x, aborter);
        } catch (SolverException e) {
            model = null;
        }
        l2 = System.nanoTime();
        //System.out.println("Time (ms) for Prop Logic to Dio model:   " + (l2-l1)/1000000);
        SatSearch.solveTime = l2 - l1;
        if (model == null) {
            SatSearch.decodeTime = 0;
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


        if (SatSearch.log.isLoggable(Level.FINEST)) {
            SatSearch.log.log(Level.FINEST, "SatSearch found the solution:\n");
        }

        Map<String, BigInteger> result;
        result = new LinkedHashMap<String, BigInteger>(conversionResult.y.size());
        IndefiniteConverter<String> bin = this.converter.getBinarizer();
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
            if (SatSearch.log.isLoggable(Level.FINEST)) {
                SatSearch.log.log(Level.FINEST, e.getKey() + "=" + coeffValue + " ");
            }
        }
        ////System.out.println(result);
        if (SatSearch.log.isLoggable(Level.FINEST)) {
            SatSearch.log.log(Level.FINEST, "\n");
        }
        l2 = System.nanoTime();
        SatSearch.decodeTime = l2 - l1;
        return result;
    }

    public class SearchInstance {
        private Formula<Diophantine> f;
        private PoloSatConverter converter;
        private Triple<Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> conversionResult;
        private Abortion aborter;
        private SATChecker satChecker;
        private Set<Variable<Diophantine>> propVars;
        private ExtendedDimacsArrayReader reader = null;
        private ISolver problem = null;


        private final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.SatSearch.SatSearch.SearchInstance");



        public SearchInstance(Formula<Diophantine> f2, PoloSatConverter converter, Triple<Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> conversionResult, Abortion aborter, SATChecker satChecker, Set<Variable<Diophantine>> propVars) {
            this.f = f2;
            this.conversionResult = conversionResult;
            this.converter = converter;
            this.aborter = aborter;
            this.satChecker = satChecker;
            this.propVars = propVars;
        }

        public Map<String, Integer> searchNext(Set<Variable<Diophantine>> propVars) {
            long l1, l2;
            l1 = System.nanoTime();
            int[] model;
            Triple<int[], ISolver, ExtendedDimacsArrayReader> trip = ((SAT4JChecker)this.satChecker).nextModel(this.conversionResult.x, this.aborter, this.problem, this.reader);
            model = trip.x;
            this.problem = trip.y;
            this.reader = trip.z;
            l2 = System.nanoTime();
            SatSearch.solveTime = l2 - l1;
            if (model == null) {
                SatSearch.decodeTime = 0;
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

            Iterator<Variable<Diophantine>> iter = propVars.iterator();
            while (iter.hasNext()) {
                if (!interpretation.contains(this.conversionResult.z.get(iter.next()).getId())) {
                    iter.remove();
                }
            }


            if (this.log.isLoggable(Level.FINEST)) {
                this.log.log(Level.FINEST, "SatSearch found the solution:\n");
            }
            IndefiniteBinarizer<String> bin = IndefiniteBinarizer.create(this.converter.getPropFactory(), this.converter.getConfig());
            Map<String, Integer> result;
            result = new LinkedHashMap<String, Integer>(this.conversionResult.y.size());
            for (Map.Entry<String, PolyCircuit> e : this.conversionResult.y.entrySet()) {
                PolyCircuit pc = e.getValue();
                List<Formula<None>> formulae = pc.getFormulae();

                int coeffValue = bin.nat(formulae, interpretation);
                if (Globals.useAssertions) {
                    if (this.converter.getTracking()) {
                        assert BigInteger.valueOf(coeffValue).compareTo(pc.getMax()) <= 0;
                    }
                }
                result.put(e.getKey(), coeffValue);
                if (this.log.isLoggable(Level.FINEST)) {
                    this.log.log(Level.FINEST, e.getKey() + "=" + coeffValue + " ");
                }
            }
            if (this.log.isLoggable(Level.FINEST)) {
                this.log.log(Level.FINEST, "\n");
            }
            l2 = System.nanoTime();
            SatSearch.decodeTime = l2 - l1;
            return result;
        }

    }

    public class IncrementalSearchInstance {

        private PoloSatConverter converter;
        private Pair<Formula<None>, Map<String, PolyCircuit>> conversionResult;
        private Abortion aborter;
        private MiniSAT2IncrementalFileChecker satChecker;


        private final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.SatSearch.SatSearch.SearchInstance");



        public IncrementalSearchInstance(PoloSatConverter converter, Pair<Formula<None>, Map<String, PolyCircuit>> conversionResult, Abortion aborter, MiniSAT2IncrementalFileChecker satChecker) {
            this.conversionResult = conversionResult;
            this.converter = converter;
            this.aborter = aborter;
            this.satChecker = satChecker;

        }

        public Map<String, BigInteger> searchNext(Set<SimplePolyConstraint> addtlConstraints, Abortion aborter) throws AbortionException {
            long l1, l2;
            l1 = System.nanoTime();

            Pair<Formula<None>, Map<String, PolyCircuit>> conversionRes2 =this.converter.convert(addtlConstraints, new LinkedHashSet<SimplePolyConstraint>(), aborter);
            int[] model;
            model = this.satChecker.solveKeepObligation(conversionRes2.x, aborter);

            if (model == null) {
                // UNSAT
                this.satChecker.finalize();
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



            if (this.log.isLoggable(Level.FINEST)) {
                this.log.log(Level.FINEST, "SatSearch found the solution:\n");
            }

            Map<String, BigInteger> result;
            result = new LinkedHashMap<String, BigInteger>(this.conversionResult.y.size());
            IndefiniteBinarizer<String> bin = IndefiniteBinarizer.create(this.converter.getPropFactory(), this.converter.getConfig());
            for (Map.Entry<String, PolyCircuit> e : this.conversionResult.y.entrySet()) {
                PolyCircuit pc = e.getValue();
                List<Formula<None>> formulae = pc.getFormulae();
                BigInteger coeffValue = bin.natBig(formulae, interpretation);
                if (Globals.useAssertions) {
                    if (this.converter.getTracking()) {
                        assert coeffValue.compareTo(pc.getMax()) <= 0;
                    }
                }
                result.put(e.getKey(), coeffValue);
                if (this.log.isLoggable(Level.FINEST)) {
                    this.log.log(Level.FINEST, e.getKey() + "=" + coeffValue + " ");
                }
            }
            if (this.log.isLoggable(Level.FINEST)) {
                this.log.log(Level.FINEST, "\n");
            }
            l2 = System.nanoTime();
            SatSearch.decodeTime = l2 - l1;
            return result;
        }


        public Map<String, BigInteger> searchFirst() {
            long l1, l2;
            l1 = System.nanoTime();

            int[] model;
            /* TODO
             * Please check how to deal with a fail here
             *
             * -- thetux
             */
            try {
                model = this.satChecker.solve(this.conversionResult.x, this.aborter, true);
            } catch (SolverException e) {
                model = null;
            } catch (AbortionException e) {
                // This is ugly.
                // BUT: The solver should check for abortions, so we have to, too
                model = null;
            }

            if (model == null) {
                // UNSAT
                this.satChecker.finalize();
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



            if (this.log.isLoggable(Level.FINEST)) {
                this.log.log(Level.FINEST, "SatSearch found the solution:\n");
            }

            Map<String, BigInteger> result;
            result = new LinkedHashMap<String, BigInteger>(this.conversionResult.y.size());
            IndefiniteBinarizer<String> bin = IndefiniteBinarizer.create(this.converter.getPropFactory(), this.converter.getConfig());
            for (Map.Entry<String, PolyCircuit> e : this.conversionResult.y.entrySet()) {
                PolyCircuit pc = e.getValue();
                List<Formula<None>> formulae = pc.getFormulae();
                BigInteger coeffValue = bin.natBig(formulae, interpretation);
                if (Globals.useAssertions) {
                    if (this.converter.getTracking()) {
                        assert coeffValue.compareTo(pc.getMax()) <= 0;
                    }
                }
                result.put(e.getKey(), coeffValue);
                if (this.log.isLoggable(Level.FINEST)) {
                    this.log.log(Level.FINEST, e.getKey() + "=" + coeffValue + " ");
                }
            }
            if (this.log.isLoggable(Level.FINEST)) {
                this.log.log(Level.FINEST, "\n");
            }
            l2 = System.nanoTime();
            SatSearch.decodeTime = l2 - l1;
            return result;
        }


        @Override
        public void finalize() {
            this.satChecker.finalize();
        }

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
    public SearchInstance multiSearch(Formula<Diophantine> f,
            PoloSatConverter converter, Abortion aborter, Set<Variable<Diophantine>> propVars)
            throws AbortionException {
        long l1, l2;
        if (converter == null) {
            converter = this.converter;
        }
        l1 = System.nanoTime();
        Triple<Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> conversionResult;
        conversionResult = converter.convert(f, aborter);
        l2 = System.nanoTime();
        SatSearch.encodeTime = l2 - l1;
        if (SatSearch.log.isLoggable(Level.FINER)) {
            SatSearch.log.log(Level.FINER, "Conversion of SimplePolyConstraints to SAT took {0} ms.\n",
                    (l2-l1)/1000000);
        }
        aborter.checkAbortion();
        SATChecker satChecker = this.satCheckerFactory.getSATChecker();
        if (!(satChecker instanceof SAT4JChecker)) {
            throw new RuntimeException("Only SAT4JChecker currently supports iterative solution searching.");
        }

        return new SearchInstance(f, converter, conversionResult, aborter, satChecker, propVars);
    }

    public boolean supportsSpecialRanges() {
        return true;
    }

    public IncrementalSearchInstance multiSearch(Set<SimplePolyConstraint> constraints, Set<SimplePolyConstraint> searchStrictConstraints,
            PoloSatConverter converter, Abortion aborter)
            throws AbortionException {
        long l1, l2;
        if (converter == null) {
            converter = this.converter;
        }
        l1 = System.nanoTime();
        Pair<Formula<None>, Map<String, PolyCircuit>> conversionResult;
        conversionResult = converter.convert(constraints, searchStrictConstraints, aborter);
        l2 = System.nanoTime();
        SatSearch.encodeTime = l2 - l1;
        if (SatSearch.log.isLoggable(Level.FINER)) {
            SatSearch.log.log(Level.FINER, "Conversion of SimplePolyConstraints to SAT took {0} ms.\n",
                    (l2-l1)/1000000);
        }
        ////System.out.println("Time for constraints to Prop Logic: " + (l2-l1)/1000000);
        aborter.checkAbortion();
        SATChecker satChecker = this.satCheckerFactory.getSATChecker();
        if (!(satChecker instanceof MiniSAT2IncrementalFileChecker)) {
            throw new RuntimeException("Only MiniSAT2IncrementalFileChecker currently supports incremental solution searching.");
        }

        return new IncrementalSearchInstance(converter, conversionResult, aborter, (MiniSAT2IncrementalFileChecker) satChecker);
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

    public boolean isMiniSAT2Incremental() {
        // TODO Auto-generated method stub
        return this.satCheckerFactory instanceof MINISAT2IncrementalEngine;
    }

    @Override
    public boolean introducesFreshVariables() {
        return false;
    }

	@Override
	public Map<String, BigInteger> searchLRA(Formula<Diophantine> fml, Abortion aborter) throws AbortionException {
		// TODO Auto-generated method stub
		return null;
	}

}
