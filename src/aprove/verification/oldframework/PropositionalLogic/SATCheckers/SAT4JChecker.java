package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.lang.reflect.*;
import java.util.*;
import java.util.logging.*;

import org.sat4j.minisat.*;
import org.sat4j.specs.*;
import org.sat4j.tools.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class SAT4JChecker implements SATChecker {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.PropositionalLogic.SATCheckers.SAT4JChecker");

    // which SAT4J solver do we use? (null means default)
    private final String library;

    public SAT4JChecker() {
        this.library = null;
    }

    /**
     * @param library - the name of SAT4J SAT solving algorithm to be used,
     *  null means default
     */
    public SAT4JChecker(final String library) {
        this.library = library;
    }

    @Override
    public int[] solve(final Formula<None> formula, final Abortion aborter) {
        return this.nextModel(formula, aborter, null, null).x;
    }

    public Triple<int[], ISolver, ExtendedDimacsArrayReader> nextModel(
        final Formula<None> formula,
        final Abortion aborter,
        ISolver problem,
        ExtendedDimacsArrayReader reader)
    {
        long l1, l2; // nanos
        l1 = System.nanoTime();
        int maxId = formula.getId();

        if (problem == null) {

            if (maxId == AbstractFormula.ID_UNSET) { // formula not labeled yet
                maxId = formula.label(1) - 1;
            }
            l2 = System.nanoTime();
            if (SAT4JChecker.log.isLoggable(Level.FINER)) {
                SAT4JChecker.log.log(Level.FINER, "Labeling the propositional formula took {0} ms.\n", (l2 - l1) / 1000000);
                SAT4JChecker.log.log(Level.FINER, "Number of ids: {0}\n", maxId);
            }
            final List<CircuitGate> gates = new ArrayList<CircuitGate>(maxId + 1);
            l1 = System.nanoTime();
            formula.addGates(gates);
            l2 = System.nanoTime();
            if (SAT4JChecker.log.isLoggable(Level.FINER)) {
                SAT4JChecker.log.log(Level.FINER, "Collecting gates took {0} ms.\n", (l2 - l1) / 1000000);
            }
            ISolver solver;
            if (this.library == null || this.library.equalsIgnoreCase("Default")) {
                solver = SolverFactory.newDefault();
                if (SAT4JChecker.log.isLoggable(Level.FINE)) {
                    SAT4JChecker.log.fine("SAT4J: Using default solver.\n");
                }
            } else {
                // a special SAT4J solver has been requested
                try {
                    solver =
                        (ISolver) MethodInvoker.invokeStaticMethod("org.sat4j.minisat.SolverFactory", "new"
                            + this.library, new Class[0], new Object[0]);
                    if (SAT4JChecker.log.isLoggable(Level.FINE)) {
                        // if we get here, it has worked.
                        SAT4JChecker.log.fine("SAT4J: Using solver " + this.library + "\n");
                    }
                } catch (final ClassNotFoundException e) {
                    solver = SolverFactory.newDefault();
                    if (SAT4JChecker.log.isLoggable(Level.FINE)) {
                        SAT4JChecker.log.fine("SAT4J: " + e + " has occurred, using default solver as fallback.\n");
                    }
                } catch (final NoSuchMethodException e) {
                    solver = SolverFactory.newDefault();
                    if (SAT4JChecker.log.isLoggable(Level.FINE)) {
                        SAT4JChecker.log.fine("SAT4J: " + e + " has occurred, using default solver as fallback.\n");
                    }
                } catch (final InvocationTargetException e) {
                    solver = SolverFactory.newDefault();
                    if (SAT4JChecker.log.isLoggable(Level.FINE)) {
                        SAT4JChecker.log.fine("SAT4J: " + e + " has occurred, using default solver as fallback.\n");
                    }
                } catch (final IllegalAccessException e) {
                    solver = SolverFactory.newDefault();
                    if (SAT4JChecker.log.isLoggable(Level.FINE)) {
                        SAT4JChecker.log.fine("SAT4J: " + e + " has occurred, using default solver as fallback.\n");
                    }
                }
            }
            ModelIterator modelIter;
            modelIter = new ModelIterator(solver);
            reader = new ExtendedDimacsArrayReader(modelIter);

            if (Globals.useAssertions) {
                assert maxId == formula.getId();
            }

            // TODO do this better! disassembling the gates is nasty.
            final int[] gateTypes = new int[gates.size() + 1];
            final int[] outputs = new int[gates.size() + 1];
            final int[][] inputs = new int[gates.size() + 1][];

            gateTypes[0] = CircuitGate.TRUE;
            outputs[0] = maxId;
            inputs[0] = CircuitGate.NO_INPUTS;

            for (int i = 0; i < gates.size(); ++i) {
                final CircuitGate g = gates.get(i);
                gateTypes[i + 1] = g.gateType;
                outputs[i + 1] = g.output;
                inputs[i + 1] = g.inputs;
                //System.out.print(g.toExtendedDimacsLine());
            }
            l1 = System.nanoTime();
            try {
                problem = reader.parseInstance(gateTypes, outputs, inputs, maxId);
            } catch (final ContradictionException ex) {
                if (SAT4JChecker.log.isLoggable(Level.CONFIG)) {
                    SAT4JChecker.log.log(Level.CONFIG, "SAT4J says: The formula is trivially unsatisfiable.\n");
                }
                return new Triple<int[], ISolver, ExtendedDimacsArrayReader>(null, null, null);
            }
            l2 = System.nanoTime();
            if (SAT4JChecker.log.isLoggable(Level.FINER)) {
                SAT4JChecker.log.log(Level.FINER, "Conversion to clauses took {0} ms.\n", (l2 - l1) / 1000000);
            }
            if (SAT4JChecker.log.isLoggable(Level.CONFIG)) {
                SAT4JChecker.log.log(Level.CONFIG, "Converting propositional formula to clauses ...\n");
            }
        }
        {

            l1 = System.nanoTime();
            final ISolver probForSolve = problem;
            final AbortionListener abortionListener = new AbortionListener() {
                @Override
                public void abortionFired(final Abortion source, final String reason) {
                    probForSolve.expireTimeout();
                }
            };
            aborter.addListenerOrFire(abortionListener);

            boolean sat = false;
            try {
                sat = problem.isSatisfiable();
            } catch (final TimeoutException e) {
                if (SAT4JChecker.log.isLoggable(Level.CONFIG)) {
                    SAT4JChecker.log.log(Level.CONFIG, "Sat solving with SAT4J timed out.\n");
                }
                sat = false;
            }
            l2 = System.nanoTime();

            if (SAT4JChecker.log.isLoggable(Level.FINER)) {
                SAT4JChecker.log.log(Level.FINER, "Satisfiability check took {0} ms.\n", (l2 - l1) / 1000000);
            }

            if (SAT4JChecker.log.isLoggable(Level.CONFIG)) {
                if (sat) {
                    SAT4JChecker.log.log(Level.CONFIG, "SAT4J says: The formula is satisfiable.\n");
                } else {
                    SAT4JChecker.log.log(Level.CONFIG, "SAT4J says: The formula is unsatisfiable.\n");
                }
            }

            if (sat) {
                // great, we have got a model for the formula!
                // now derive the coefficient values.
                final int[] model = problem.model();
                abortionListener.deregisterWithAbortion();
                return new Triple<int[], ISolver, ExtendedDimacsArrayReader>(model, problem, reader);
            }
            abortionListener.deregisterWithAbortion();
        }

        return new Triple<int[], ISolver, ExtendedDimacsArrayReader>(null, problem, reader);
    }

    /**
     * Finds <b>all</b> models of formula.
     * Probably only useful for debug purposes.
     *
     * @param formula
     * @return a list that contains all the models of formula
     *  (the empty list if there is no model)
     */
    public List<int[]> findAllModels(final Formula<None> formula) {
        long l1, l2; // nanos
        l1 = System.nanoTime();
        int maxId = formula.getId();
        if (maxId == AbstractFormula.ID_UNSET) { // formula not labeled yet
            maxId = formula.label(1) - 1;
        }
        l2 = System.nanoTime();
        if (SAT4JChecker.log.isLoggable(Level.FINER)) {
            SAT4JChecker.log.log(Level.FINER, "Labeling the propositional formula took {0} ms.\n", (l2 - l1) / 1000000);
            SAT4JChecker.log.log(Level.FINER, "Number of ids: {0}\n", maxId);
        }
        final List<CircuitGate> gates = new ArrayList<CircuitGate>(maxId + 1);
        l1 = System.nanoTime();
        formula.addGates(gates);
        l2 = System.nanoTime();
        if (SAT4JChecker.log.isLoggable(Level.FINER)) {
            SAT4JChecker.log.log(Level.FINER, "Collecting gates took {0} ms.\n", (l2 - l1) / 1000000);
        }
        final ISolver solver = SolverFactory.newDefault();
        ModelIterator modelIter;
        modelIter = new ModelIterator(solver);
        final ExtendedDimacsArrayReader reader = new ExtendedDimacsArrayReader(modelIter);

        if (Globals.useAssertions) {
            assert maxId == formula.getId();
        }

        // TODO do this better! disassembling the gates is nasty.
        final int[] gateTypes = new int[gates.size() + 1];
        final int[] outputs = new int[gates.size() + 1];
        final int[][] inputs = new int[gates.size() + 1][];

        gateTypes[0] = CircuitGate.TRUE;
        outputs[0] = maxId;
        inputs[0] = CircuitGate.NO_INPUTS;

        for (int i = 0; i < gates.size(); ++i) {
            final CircuitGate g = gates.get(i);
            gateTypes[i + 1] = g.gateType;
            outputs[i + 1] = g.output;
            inputs[i + 1] = g.inputs;
        }

        List<int[]> result;
        result = new ArrayList<int[]>();

        try {
            SAT4JChecker.log.log(Level.CONFIG, "Converting propositional formula to clauses ...\n");
            l1 = System.nanoTime();
            final IProblem problem = reader.parseInstance(gateTypes, outputs, inputs, maxId);
            l2 = System.nanoTime();
            if (SAT4JChecker.log.isLoggable(Level.FINER)) {
                SAT4JChecker.log.log(Level.FINER, "Conversion to clauses took {0} ms.\n", (l2 - l1) / 1000000);
            }
            l1 = System.nanoTime();
            while (problem.isSatisfiable()) {
                final int[] model = problem.model();
                result.add(model);
            }
            l2 = System.nanoTime();

            if (SAT4JChecker.log.isLoggable(Level.FINER)) {
                SAT4JChecker.log.log(Level.FINER, "Getting all " + result.size() + " models took {0} ms.\n", (l2 - l1) / 1000000);
            }
        } catch (final ContradictionException e) {
            if (SAT4JChecker.log.isLoggable(Level.CONFIG)) {
                SAT4JChecker.log.log(Level.CONFIG, "The formula is trivially unsatisfiable.\n");
            }
        } catch (final TimeoutException e) {
            if (SAT4JChecker.log.isLoggable(Level.CONFIG)) {
                SAT4JChecker.log.log(Level.CONFIG, "Sat solving timed out.\n");
            }
        }
        return result;
    }

    @Override
    public int[] solveCNF(final Formula<None> formula, final Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void setAssumps(final Set<Formula<None>> assumps) {
        // Nothing to be done.

    }

    @Override
    public int[] solve(final String dimacs, final Abortion aborter) throws AbortionException {
        // TODO Auto-generated method stub
        throw new UnsupportedOperationException("Not yet implemented");
    }

}
