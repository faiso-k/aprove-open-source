package aprove.verification.oldframework.PropositionalLogic;

import static aprove.verification.oldframework.PropositionalLogic.CircuitGate.*;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import org.sat4j.core.*;
import org.sat4j.specs.*;
import org.sat4j.tools.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.PropositionalLogic.Translation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Functional class which offers a method to convert a propositional formula
 * to an equivalent String either in Dimacs format or in Extended Dimacs
 * format. If the formula has not been labeled before, it will be labeled by
 * the conversion method.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class FormulaToDimacsConverter {

    private static Logger log = Logger.getLogger("aprove.verification.oldframework.PropositionalLogic.FormulaToDimacsConverter");

    // for gates specified in rawEDimacs
    public final static char iscasGatePrefix = 'g';

    // we need to express iff, xor, ite via and, or, not;
    // thus, additional gate names are needed
    public final static char addIscasGatePrefix = 'h';

    private final static int ABORTION_FREQUENCY = 127;

    /**
     * Applies Tseitin's algorithm on formula and returns the resulting
     * CNF as a Dimacs String. Currently uses the implementation provided
     * by the SAT4J project.
     *
     * @param formula - to be converted to Dimacs format
     * @return a sufficiently equisatisfiable Dimacs CNF representation
     *  of formula
     */
    public static String convert(final Formula<None> formula, final Abortion aborter) throws AbortionException {
        return FormulaToDimacsConverter.convert(formula, false, aborter);

    }

    /**
     * Applies our own implementation of Tseitin's algorithm, bypassing all intermediate steps.
     * @param output
     * @param formula
     */
    public static void convertAndWrite(final File output, final Formula<None> formula) throws IOException {
        final DimacsGenerator dgen = new DimacsGenerator(output);
        final Tseitinizer ts = new Tseitinizer(dgen);
        final aprove.verification.oldframework.PropositionalLogic.Formulae.FormulaTranslator translate =
            new aprove.verification.oldframework.PropositionalLogic.Formulae.FormulaTranslator(ts);

        // Translate the formula to DIMACS using Tseitin's algorithm
        formula.apply(translate);
        // add the master gate
        translate.finish(formula);
        // and add the neccessary DIMACS metadata
        dgen.postProcess(formula.getId());

    }

    /**
     * Applies Tseitin's algorithm on formula and returns the resulting
     * CNF as a Dimacs String. Currently uses the implementation provided
     * by the SAT4J project.
     *
     * Uses xorClauses for XOR if xorClauses is set to true
     *
     * @param formula - to be converted to Dimacs format
     * @param xorClauses - true for xorClauses (non-standard),
     *  false for standard DIMACS format as in the SAT competitions
     * @return a sufficiently equisatisfiable Dimacs CNF representation
     *  of formula
     */
    public static String convert(final Formula<None> formula, final boolean xorClauses, final Abortion aborter)
        throws AbortionException
    {
        long l1, l2; // nanos
        Quadruple<int[], int[], int[][], Integer> rawEDimacs;
        rawEDimacs = FormulaToDimacsConverter.toEDimacsArrays(formula, aborter);
        final int[] gateTypes = rawEDimacs.w;
        final int[] outputs = rawEDimacs.x;
        final int[][] inputs = rawEDimacs.y;
        final int maxId = rawEDimacs.z;
        aborter.checkAbortion();

        String result;

        try {
            l1 = System.nanoTime();
            if (true) { // OLD STYLE
                //ExtendedDimacsArrayToDimacsConverter reader = new ExtendedDimacsArrayToDimacsConverter(7*maxId);
                final ExtendedDimacsArrayToDimacsConverter reader =
                    new ExtendedDimacsArrayToDimacsConverter(7 * maxId, xorClauses);
                final AbortionListener abortionListener = new AbortionListener() {
                    @Override
                    public void abortionFired(final Abortion source, final String reason) {
                        // make sure you have the latest sat4j code checked out!
                        reader.expireTimeout();
                    }
                };
                aborter.addListenerOrFire(abortionListener);
                try {
                    result = reader.parseInstance(gateTypes, outputs, inputs, maxId);
                } catch (final TimeoutException e) {
                    assert (aborter.isAborted());
                    throw new AbortionException(aborter.getAbortionReason());
                }
                abortionListener.deregisterWithAbortion();
            } else { // DimacsStringSolver
                final DimacsStringSolver dimacsStringSolver = new DimacsStringSolver(7 * maxId);
                final GateTranslator gater = new GateTranslator(dimacsStringSolver);
                gater.newVar(maxId);
                final int max = outputs.length;
                for (int i = 0; i < max; ++i) {
                    switch (gateTypes[i]) {
                    case FALSE:
                        if (Globals.useAssertions) {
                            assert inputs[i].length == 0;
                        }
                        gater.gateFalse(outputs[i]);
                        break;
                    case TRUE:
                        if (Globals.useAssertions) {
                            assert inputs[i].length == 0;
                        }
                        gater.gateTrue(outputs[i]);
                        break;
                    case OR:
                        gater.or(outputs[i], new VecInt(inputs[i]));
                        break;
                    case NOT:
                        if (Globals.useAssertions) {
                            assert inputs[i].length == 1;
                        }
                        gater.not(outputs[i], inputs[i][0]);
                        break;
                    case AND:
                        gater.and(outputs[i], new VecInt(inputs[i]));
                        break;
                    case XOR:
                        gater.xor(outputs[i], new VecInt(inputs[i]));
                        break;
                    case IFF:
                        gater.iff(outputs[i], new VecInt(inputs[i]));
                        break;
                    case IFTHENELSE:
                        if (Globals.useAssertions) {
                            assert inputs[i].length == 3;
                        }
                        gater.ite(outputs[i], inputs[i][0], inputs[i][1], inputs[i][2]);
                        break;
                    default:
                        throw new UnsupportedOperationException("Gate type " + gateTypes[i] + " not handled yet");
                    }
                    if ((i & FormulaToDimacsConverter.ABORTION_FREQUENCY) == 0) { // check aborter every now and then
                        aborter.checkAbortion();
                    }
                }
                result = dimacsStringSolver.toString();
            }
            l2 = System.nanoTime();
            if (FormulaToDimacsConverter.log.isLoggable(Level.FINER)) {
                FormulaToDimacsConverter.log.log(Level.FINER, "Conversion of gates to Dimacs format took {0} ms.\n", (l2 - l1) / 1000000);
            }
            aborter.checkAbortion();
        } catch (final ContradictionException e) {
            // should never happen, we only convert, we do not solve
            if (Globals.useAssertions) {
                assert false;
            }
            result = null;
        }
        return result;
    }

    public static Pair<String, String> convertReverse(
        final Formula<None> formula,
        final boolean xorClauses,
        final Abortion aborter) throws AbortionException
    {
        long l1, l2; // nanos
        Quadruple<int[], int[], int[][], Integer> rawEDimacs;
        rawEDimacs = FormulaToDimacsConverter.toEDimacsArrays(formula, aborter);
        final int[] gateTypes = rawEDimacs.w;
        final int[] outputs = rawEDimacs.x;
        final int[][] inputs = rawEDimacs.y;
        final int maxId = rawEDimacs.z;

        String result;
        String resultReverse;

        try {
            l1 = System.nanoTime();
            final ExtendedDimacsArrayToDimacsReverseConverter reader =
                new ExtendedDimacsArrayToDimacsReverseConverter(7 * maxId, xorClauses);
            final DimacsArrayToDimacsReverseConverter.Pair<String, String> resultPair =
                reader.parseInstance(gateTypes, outputs, inputs, maxId);
            result = resultPair.x;
            resultReverse = resultPair.y;
            l2 = System.nanoTime();
            if (FormulaToDimacsConverter.log.isLoggable(Level.FINER)) {
                FormulaToDimacsConverter.log.log(Level.FINER, "Conversion of gates to Dimacs format took {0} ms.\n", (l2 - l1) / 1000000);
            }
        } catch (final ContradictionException e) {
            // should never happen, we only convert, we do not solve
            if (Globals.useAssertions) {
                assert false;
            }
            result = null;
            resultReverse = null;
        }
        return new Pair<String, String>(result, resultReverse);
    }

    /**
     * Applies Tseitin's algorithm on formula and returns the resulting
     * CNF as a Dimacs String. Currently uses the implementation provided
     * by the SAT4J project.
     *
     * Also adds weights to "SpecialANDs" for partial Max-SAT solving.
     *
     * @param formula - to be converted to Dimacs format (hard clauses)
     * @return a sufficiently equisatisfiable Dimacs CNF representation
     *  of formula
     */
    public static String convertPMax(final Formula<None> formula, final Collection<Formula<None>> maxSatFormulas) {
        long l1, l2; // nanos
        Quadruple<int[], int[], int[][], Integer> rawEDimacs;
        Pair<int[], Quadruple<int[], int[], int[][], Integer>> pair;
        pair = FormulaToDimacsConverter.toEDimacsArraysPMax(formula, maxSatFormulas);
        rawEDimacs = pair.y;
        final int[] maxSatArray = pair.x;

        final int[] gateTypes = rawEDimacs.w;
        final int[] outputs = rawEDimacs.x;
        final int[][] inputs = rawEDimacs.y;
        final int maxId = rawEDimacs.z;

        String result;

        try {
            l1 = System.nanoTime();
            final PMaxDimacsConverter reader = new PMaxDimacsConverter(7 * maxId);
            result = reader.parseInstance(gateTypes, outputs, inputs, maxId);
            l2 = System.nanoTime();
            if (FormulaToDimacsConverter.log.isLoggable(Level.FINER)) {
                FormulaToDimacsConverter.log.log(Level.FINER, "Conversion of gates to Dimacs format took {0} ms.\n", (l2 - l1) / 1000000);
            }
            for (final int element : maxSatArray) {
                result += "1 " + element + " 0\n";
            }
        } catch (final ContradictionException e) {
            // should never happen, we only convert, we do not solve
            if (Globals.useAssertions) {
                assert false;
            }
            result = null;
        }
        return result;
    }

    private static Quadruple<int[], int[], int[][], Integer> toEDimacsArrays(
        final Formula<None> formula,
        final Abortion aborter) throws AbortionException
    {
        long l1, l2; // nanos
        aborter.checkAbortion();
        l1 = System.nanoTime();
        int maxId = formula.getId();
        if (maxId == AbstractFormula.ID_UNSET) { // formula has not been labeled yet
            maxId = formula.label(1) - 1;
        }
        l2 = System.nanoTime();
        aborter.checkAbortion();
        if (FormulaToDimacsConverter.log.isLoggable(Level.FINER)) {
            FormulaToDimacsConverter.log.log(Level.FINER, "Labeling the propositional formula took {0} ms.\n", (l2 - l1) / 1000000);
            FormulaToDimacsConverter.log.log(Level.FINER, "Number of ids: {0}\n", maxId);
        }
        final List<CircuitGate> gates = new ArrayList<CircuitGate>(maxId + 1);
        l1 = System.nanoTime();
        formula.addGates(gates);
        l2 = System.nanoTime();
        aborter.checkAbortion();
        if (FormulaToDimacsConverter.log.isLoggable(Level.FINER)) {
            FormulaToDimacsConverter.log.log(Level.FINER, "Collecting gates took {0} ms.\n", (l2 - l1) / 1000000);
        }

        final int gatesSize = gates.size();
        final int[] gateTypes = new int[gatesSize + 1];
        final int[] outputs = new int[gatesSize + 1];
        final int[][] inputs = new int[gatesSize + 1][];

        gateTypes[0] = CircuitGate.TRUE;
        outputs[0] = maxId;
        inputs[0] = CircuitGate.NO_INPUTS;

        for (int i = 0; i < gatesSize; ++i) {
            final CircuitGate g = gates.get(i);
            gateTypes[i + 1] = g.gateType;
            outputs[i + 1] = g.output;
            inputs[i + 1] = g.inputs;
            if ((i & FormulaToDimacsConverter.ABORTION_FREQUENCY) == 0) { // check aborter every now and then
                aborter.checkAbortion();
            }
        }

        final Quadruple<int[], int[], int[][], Integer> result =
            new Quadruple<int[], int[], int[][], Integer>(gateTypes, outputs, inputs, maxId);

        if (false) { // GENERATE EDIMACS FOR SAT '07
            final String edimacs = FormulaToDimacsConverter.toExtendedDimacs(result, aborter);
            try {
                final File edimacsDir = new File("/home/fuhs/noncnf");
                final File input = File.createTempFile("aprove", ".ncnf", edimacsDir);
                final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
                inputWriter.write(edimacs);
                inputWriter.close();
                FormulaToDimacsConverter.log.log(Level.FINER, "EDIMACS to {0}\n", input.getCanonicalPath());
            } catch (final IOException e) {
                FormulaToDimacsConverter.log.warning("Writing EDIMACS failed!");
            }
        }
        return result;
    }

    private static Pair<int[], Quadruple<int[], int[], int[][], Integer>> toEDimacsArraysPMax(
        final Formula<None> formula,
        final Collection<Formula<None>> maxSatFormulas)
    {
        long l1, l2; // nanos
        l1 = System.nanoTime();
        int maxId = formula.getId();
        if (maxId == AbstractFormula.ID_UNSET) { // formula has not been labeled yet
            maxId = formula.label(1) - 1;
        }
        final int[] maxSatArray = new int[maxSatFormulas.size()];
        int i = 0;
        for (final Formula<None> form : maxSatFormulas) {
            maxSatArray[i] = form.getId();
            i++;
        }

        l2 = System.nanoTime();
        if (FormulaToDimacsConverter.log.isLoggable(Level.FINER)) {
            FormulaToDimacsConverter.log.log(Level.FINER, "Labeling the propositional formula took {0} ms.\n", (l2 - l1) / 1000000);
            FormulaToDimacsConverter.log.log(Level.FINER, "Number of ids: {0}\n", maxId);
        }
        final List<CircuitGate> gates = new ArrayList<CircuitGate>(maxId + 1);
        l1 = System.nanoTime();
        formula.addGates(gates);
        l2 = System.nanoTime();
        if (FormulaToDimacsConverter.log.isLoggable(Level.FINER)) {
            FormulaToDimacsConverter.log.log(Level.FINER, "Collecting gates took {0} ms.\n", (l2 - l1) / 1000000);
        }

        final int gatesSize = gates.size();
        final int[] gateTypes = new int[gatesSize + 1];
        final int[] outputs = new int[gatesSize + 1];
        final int[][] inputs = new int[gatesSize + 1][];

        gateTypes[0] = CircuitGate.TRUE;
        outputs[0] = maxId;
        inputs[0] = CircuitGate.NO_INPUTS;

        for (i = 0; i < gatesSize; ++i) {
            final CircuitGate g = gates.get(i);
            gateTypes[i + 1] = g.gateType;
            outputs[i + 1] = g.output;
            inputs[i + 1] = g.inputs;
        }

        final Quadruple<int[], int[], int[][], Integer> result =
            new Quadruple<int[], int[], int[][], Integer>(gateTypes, outputs, inputs, maxId);
        return new Pair<int[], Quadruple<int[], int[], int[][], Integer>>(maxSatArray, result);
    }

    /**
     * Writes a Dimacs CNF representation of formula to pw
     * (-> Tseitin's algorithm). Uses SAT4J's DimacsOutputSolver.
     *
     * @param formula - to be represented as a Dimacs CNF
     * @param pw - target for the CNF
     */
    public static void convert(final Formula<None> formula, final PrintWriter pw, final Abortion aborter)
        throws AbortionException
    {
        long l1, l2; // nanos

        Quadruple<int[], int[], int[][], Integer> rawEDimacs;
        rawEDimacs = FormulaToDimacsConverter.toEDimacsArrays(formula, aborter);
        final int[] gateTypes = rawEDimacs.w;
        final int[] outputs = rawEDimacs.x;
        final int[][] inputs = rawEDimacs.y;
        final int maxId = rawEDimacs.z;

        final DimacsOutputSolver solver = new DimacsOutputSolver(pw);
        final ExtendedDimacsArrayReader reader = new ExtendedDimacsArrayReader(solver);
        try {
            l1 = System.nanoTime();
            reader.parseInstance(gateTypes, outputs, inputs, maxId);
            l2 = System.nanoTime();
            if (FormulaToDimacsConverter.log.isLoggable(Level.FINER)) {
                FormulaToDimacsConverter.log.log(Level.FINER, "Conversion of gates to Dimacs format took {0} ms.\n", (l2 - l1) / 1000000);
            }
            aborter.checkAbortion();
        } catch (final ContradictionException e) {
            // should never happen, we only convert, we do not solve
            if (Globals.useAssertions) {
                assert false;
            }
        }
    }

    /**
     * Converts formula to Extended Dimacs format.
     * Side effect: Labels formula in the process.
     *
     * @param formula - to be converted to Extended Dimacs format
     * @return a String representation of formula in Extended Dimacs format
     */
    public static String convertToExtendedDimacs(final Formula<None> formula, final Abortion aborter)
        throws AbortionException
    {
        Quadruple<int[], int[], int[][], Integer> rawEDimacs;
        rawEDimacs = FormulaToDimacsConverter.toEDimacsArrays(formula, aborter);
        final int[] gateTypes = rawEDimacs.w;
        final int[] outputs = rawEDimacs.x;
        final int[][] inputs = rawEDimacs.y;
        final int maxId = rawEDimacs.z;

        if (Globals.useAssertions) {
            assert gateTypes.length == outputs.length;
            assert gateTypes.length == inputs.length;
        }

        aborter.checkAbortion();
        final StringBuilder result = new StringBuilder(20 * maxId);
        result.append("p noncnf ");
        result.append(maxId);
        result.append('\n');
        final int length = gateTypes.length;
        for (int i = 1; i < length; ++i) {
            result.append(gateTypes[i]);
            result.append(" -1 ");
            result.append(outputs[i]);
            result.append(' ');
            final int inputsILength = inputs[i].length;
            for (int j = 0; j < inputsILength; ++j) {
                result.append(inputs[i][j]);
                result.append(' ');
            }
            result.append("0\n");
            if ((i & FormulaToDimacsConverter.ABORTION_FREQUENCY) == 0) { // check aborter every now and then
                aborter.checkAbortion();
            }
        }
        return result.toString();
    }

    /**
     * Converts rawEDimacs to an Extended Dimacs format String.
     *
     * @param rawEDimacs - to be converted to Extended Dimacs format
     * @return a String representation of rawEDimacs in Extended Dimacs format
     */
    private static String toExtendedDimacs(
        final Quadruple<int[], int[], int[][], Integer> rawEDimacs,
        final Abortion aborter) throws AbortionException
    {
        final int[] gateTypes = rawEDimacs.w;
        final int[] outputs = rawEDimacs.x;
        final int[][] inputs = rawEDimacs.y;
        final int maxId = rawEDimacs.z;

        if (Globals.useAssertions) {
            assert gateTypes.length == outputs.length;
            assert gateTypes.length == inputs.length;
        }

        final StringBuilder result = new StringBuilder(10 * maxId);
        result.append("p noncnf ");
        result.append(maxId);
        result.append('\n');
        final int length = gateTypes.length;
        for (int i = 1; i < length; ++i) {
            result.append(gateTypes[i]);
            result.append(" -1 ");
            result.append(outputs[i]);
            result.append(' ');
            final int inputsILength = inputs[i].length;
            for (int j = 0; j < inputsILength; ++j) {
                result.append(inputs[i][j]);
                result.append(' ');
            }
            result.append("0\n");
            if ((i & FormulaToDimacsConverter.ABORTION_FREQUENCY) == 0) { // check aborter every now and then
                aborter.checkAbortion();
            }
        }
        return result.toString();
    }

    public static String convertToIscas(final Formula<None> formula, final Abortion aborter) throws AbortionException {
        Quadruple<int[], int[], int[][], Integer> rawEDimacs;
        rawEDimacs = FormulaToDimacsConverter.toEDimacsArrays(formula, aborter);
        return FormulaToDimacsConverter.extendedDimacsToIscas(rawEDimacs);
    }

    /**
     * Iscas is another (somewhat) popular format for representing Boolean
     * circuits in the context of hardware verification.
     *
     * TODO deal with Boolean constants which are not at the root of the
     * formula in some way.
     *
     * @param rawEDimacs - <type, output, inputs, maxId>; entry[0] is ignored
     * @return a corresponding ISCAS String with only AND, OR, NOT as junctors
     *  (as presumably accepted by NoClause by Bacchus and Walsh); any ISCAS
     *  gate specification seems to require that its input has already been
     *  specified before (should not be a problem for us, see related methods
     *  of this class)
     */
    private static String extendedDimacsToIscas(final Quadruple<int[], int[], int[][], Integer> rawEDimacs) {
        int addGateIndex = 1;
        final StringBuilder res = new StringBuilder();
        final int[] gateTypes = rawEDimacs.w;
        final int[] outputs = rawEDimacs.x;
        final int[][] inputs = rawEDimacs.y;
        final int maxId = rawEDimacs.z;

        // special handling for the two formulae TRUE and FALSE at the root:
        if (maxId == 1) {
            if (gateTypes[1] == CircuitGate.TRUE) {
                // SAT
                final String pf = Character.toString(FormulaToDimacsConverter.addIscasGatePrefix);
                return "INPUT(" + pf + "1)\nOUTPUT(" + pf + "2)\n" + pf + "2 = OR(" + pf + "1," + pf + "1)\n";
            } else if (gateTypes[1] == CircuitGate.FALSE) {
                // UNSAT, but no contradictions in any single clause
                final String pf = Character.toString(FormulaToDimacsConverter.addIscasGatePrefix);
                return "INPUT("
                    + pf
                    + "1)\nOUTPUT("
                    + pf
                    + "2)\n"
                    + pf
                    + "3 = NOT("
                    + pf
                    + "1)\n"
                    + pf
                    + "2 = AND("
                    + pf
                    + "1,"
                    + pf
                    + "3)\n";
            }
        }

        final int[] iscasNodeTypes = new int[maxId + 1];
        Arrays.fill(iscasNodeTypes, -1);
        // nodeType[i] = ...
        //           1 if i is an input id
        //           2 if i is an inner node id
        //           3 if i is the master output
        //          -1 if undefined
        final int INPUT = 1;
        final int INNER_NODE = 2;
        final int OUTPUT = 3;

        // 1) look for input nodes
        for (int i = 1; i < inputs.length; ++i) {
            final int[] inputVector = inputs[i];
            for (int j = 0; j < inputVector.length; ++j) {
                iscasNodeTypes[inputVector[j]] = INPUT;
            }
        }

        // 2) look for non-input nodes (inner or master output):
        //    many of the previously found "inputs" are actually inner nodes
        for (int i = 1; i < outputs.length; ++i) {
            if (Globals.useAssertions) {
                assert iscasNodeTypes[outputs[i]] == INPUT || outputs[i] == maxId;
            }
            iscasNodeTypes[outputs[i]] = INNER_NODE;
        }

        // 3) by def, max must be the master output
        iscasNodeTypes[maxId] = OUTPUT;

        // okay, now we can gather the info on the inputs and the master output
        for (int i = 1; i < iscasNodeTypes.length; ++i) {
            switch (iscasNodeTypes[i]) {
            case INPUT:
                res.append("INPUT(");
                res.append(FormulaToDimacsConverter.iscasGatePrefix);
                res.append(i);
                res.append(")\n");
                break;
            case OUTPUT:
                res.append("OUTPUT(");
                res.append(FormulaToDimacsConverter.iscasGatePrefix);
                res.append(i);
                res.append(")\n");
                break;
            default:
                break;
            }
        }

        // now write the actual gate definitions
        // start at the end of the list to make sure that everything
        // is defined before it is used!
        for (int i = outputs.length - 1; i >= 1; --i) {
            switch (gateTypes[i]) {
            case CircuitGate.NOT: {
                if (Globals.useAssertions) { // must be unary
                    assert inputs[i].length == 1;
                }
                res.append(FormulaToDimacsConverter.iscasGatePrefix).append(outputs[i]).append(" = NOT(");
                res.append(FormulaToDimacsConverter.iscasGatePrefix).append(inputs[i][0]);
                break;
            }
            case CircuitGate.AND: {
                if (Globals.useAssertions) { // must be at least binary
                    assert inputs[i].length >= 2;
                }
                res.append(FormulaToDimacsConverter.iscasGatePrefix).append(outputs[i]).append(" = AND(");
                boolean first = true;
                for (int j = 0; j < inputs[i].length; ++j) {
                    if (first) {
                        first = false;
                    } else {
                        res.append(", ");
                    }
                    res.append(FormulaToDimacsConverter.iscasGatePrefix).append(inputs[i][j]);
                }
                break;
            }
            case CircuitGate.OR: {
                if (Globals.useAssertions) { // must be at least binary
                    assert inputs[i].length >= 2;
                }
                res.append(FormulaToDimacsConverter.iscasGatePrefix).append(outputs[i]).append(" = OR(");
                boolean first = true;
                for (int j = 0; j < inputs[i].length; ++j) {
                    if (first) {
                        first = false;
                    } else {
                        res.append(", ");
                    }
                    res.append(FormulaToDimacsConverter.iscasGatePrefix).append(inputs[i][j]);
                }
                break;
            }
            case CircuitGate.IFF: { // must be binary for us
                /*
                if (Globals.useAssertions) {
                    assert inputs[i].length >= 2;
                }
                res.append("XNOR(");
                boolean first = true;
                for (int j = 0; j < inputs[i].length; ++j) {
                    if (first) {
                        first = false;
                    }
                    else {
                        res.append(", ");
                    }
                    res.append(iscasGatePrefix).append(inputs[i][j]);
                }
                */
                if (Globals.useAssertions) {
                    assert inputs[i].length == 2;
                }
                StringBuilder both, none, notFirst, notSecond; // new nodes
                notFirst = new StringBuilder().append(FormulaToDimacsConverter.addIscasGatePrefix).append(addGateIndex++);
                notSecond = new StringBuilder().append(FormulaToDimacsConverter.addIscasGatePrefix).append(addGateIndex++);

                res.append(notFirst).append(" = NOT(").append(FormulaToDimacsConverter.iscasGatePrefix).append(inputs[i][0]).append(")\n");
                res.append(notSecond).append(" = NOT(").append(FormulaToDimacsConverter.iscasGatePrefix).append(inputs[i][1]).append(")\n");

                both = new StringBuilder().append(FormulaToDimacsConverter.addIscasGatePrefix).append(addGateIndex++);
                none = new StringBuilder().append(FormulaToDimacsConverter.addIscasGatePrefix).append(addGateIndex++);

                res
                    .append(both)
                    .append(" = AND(")
                    .append(FormulaToDimacsConverter.iscasGatePrefix)
                    .append(inputs[i][0])
                    .append(", ")
                    .append(FormulaToDimacsConverter.iscasGatePrefix)
                    .append(inputs[i][1])
                    .append(")\n");
                res.append(none).append(" = AND(").append(notFirst).append(", ").append(notSecond).append(")\n");

                res.append(FormulaToDimacsConverter.iscasGatePrefix).append(outputs[i]).append(" = OR(").append(both).append(", ").append(none);
                break;
            }
            case CircuitGate.XOR: { // must be binary for us
                /*
                if (Globals.useAssertions) {
                    assert inputs[i].length >= 2;
                }
                res.append("XOR(");
                boolean first = true;
                for (int j = 0; j < inputs[i].length; ++j) {
                    if (first) {
                        first = false;
                    }
                    else {
                        res.append(", ");
                    }
                    res.append(iscasGatePrefix).append(inputs[i][j]);
                }
                */
                if (Globals.useAssertions) {
                    assert inputs[i].length == 2;
                }

                StringBuilder onlyFirstOne, onlySecondOne, notFirst, notSecond; // new nodes
                notFirst = new StringBuilder().append(FormulaToDimacsConverter.addIscasGatePrefix).append(addGateIndex++);
                notSecond = new StringBuilder().append(FormulaToDimacsConverter.addIscasGatePrefix).append(addGateIndex++);

                res.append(notFirst).append(" = NOT(").append(FormulaToDimacsConverter.iscasGatePrefix).append(inputs[i][0]).append(")\n");
                res.append(notSecond).append(" = NOT(").append(FormulaToDimacsConverter.iscasGatePrefix).append(inputs[i][1]).append(")\n");

                onlyFirstOne = new StringBuilder().append(FormulaToDimacsConverter.addIscasGatePrefix).append(addGateIndex++);
                onlySecondOne = new StringBuilder().append(FormulaToDimacsConverter.addIscasGatePrefix).append(addGateIndex++);

                res
                    .append(onlyFirstOne)
                    .append(" = AND(")
                    .append(FormulaToDimacsConverter.iscasGatePrefix)
                    .append(inputs[i][0])
                    .append(", ")
                    .append(notSecond)
                    .append(")\n");
                res
                    .append(onlySecondOne)
                    .append(" = AND(")
                    .append(notFirst)
                    .append(", ")
                    .append(FormulaToDimacsConverter.iscasGatePrefix)
                    .append(inputs[i][1])
                    .append(")\n");

                res
                    .append(FormulaToDimacsConverter.iscasGatePrefix)
                    .append(outputs[i])
                    .append(" = OR(")
                    .append(onlyFirstOne)
                    .append(", ")
                    .append(onlySecondOne);
                break;
            }
            case CircuitGate.IFTHENELSE: {
                if (Globals.useAssertions) { // must be ternary
                    assert inputs[i].length == 3;
                }
                StringBuilder case1, case2, notCond; // new nodes
                case1 = new StringBuilder().append(FormulaToDimacsConverter.addIscasGatePrefix).append(addGateIndex++);
                notCond = new StringBuilder().append(FormulaToDimacsConverter.addIscasGatePrefix).append(addGateIndex++);
                case2 = new StringBuilder().append(FormulaToDimacsConverter.addIscasGatePrefix).append(addGateIndex++);

                res
                    .append(case1)
                    .append(" = AND(")
                    .append(FormulaToDimacsConverter.iscasGatePrefix)
                    .append(inputs[i][0])
                    .append(", ")
                    .append(FormulaToDimacsConverter.iscasGatePrefix)
                    .append(inputs[i][1])
                    .append(")\n");
                res.append(notCond).append(" = NOT(").append(FormulaToDimacsConverter.iscasGatePrefix).append(inputs[i][0]).append(")\n");
                res.append(case2).append(" = AND(").append(notCond).append(", ").append(inputs[i][2]).append(")\n");

                res
                    .append(FormulaToDimacsConverter.iscasGatePrefix)
                    .append(outputs[i])
                    .append(" = OR(")
                    .append(case1)
                    .append(", ")
                    .append(case2);
                break;
            }
            default:
                FormulaToDimacsConverter.log.fine("Cannot handle gate type " + gateTypes[i]);
                throw new RuntimeException("Cannot handle gate type " + gateTypes[i]);
            }
            res.append(")\n");
        }
        return res.toString();
    }
}
