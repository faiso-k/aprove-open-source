package aprove.solver.Engines;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;
import aprove.verification.oldframework.SMT.Solver.SMTInterpol.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.SMTUtility.*;
import de.uni_freiburg.informatik.ultimate.logic.*;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.*;

/**
 * SMTInterpol is an SMT solver written in Java and released under
 * LGPL license:
 *
 * http://ultimate.informatik.uni-freiburg.de/smtinterpol/
 *
 * It participated at SMT-COMP 2012, and it supports the logics
 * QF_LIA, QF_LRA, QF_UF, QF_UFLIA, QF_UFLRA, and QF_UFLIRA
 * (here both integer and real variables may occur).
 *
 * On "easy" instances, calling SMTInterpol should be considerably
 * faster than a call to an external solver like Z3 or Yices:
 * No external process needs to be spawned, and the SMT instances
 * are passed internally to SMTInterpol, not via hard disk.
 *
 * An interesting feature (that we do not use yet) is that SMTInterpol
 * also supports interpolation for QF_LIA and QF_UFLIA.
 *
 * @author Carsten Fuhs
 */
public class SMTInterpolEngine extends SMTEngine {

    /** Arguments for the SMTInterpolEngine. */
    public static class Arguments extends SMTEngine.Arguments {
        // Nothing much so far.
    }

    /** The log facility used for debugging stuff. */
    private static final Logger LOG =
        Logger.getLogger("aprove.solver.Engines.SMTInterpolEngine");

    /**
     * @param arguments for the superclass
     */
    @ParamsViaArgumentObject
    public SMTInterpolEngine(final Arguments arguments) {
        super(arguments);
    }

    /* (non-Javadoc)
     * @see aprove.solver.Engines.SMTEngine#satisfiable(java.util.List, aprove.solver.Engines.SMTEngine.SMTLogic, aprove.strategies.Abortions.Abortion)
     */
    @Override
    public YNM satisfiable(final List<Formula<SMTLIBTheoryAtom>> formulas, final SMTLogic logic, final Abortion aborter)
            throws AbortionException, WrongLogicException {
        return this.solveAndPutIntoFormula(formulas, logic, aborter);
    }

    /* (non-Javadoc)
     * @see aprove.solver.Engines.SMTEngine#solve(java.util.List, aprove.solver.Engines.SMTEngine.SMTLogic, aprove.strategies.Abortions.Abortion)
     */
    @Override
    public Pair<YNM, Map<String, String>> solve(final List<Formula<SMTLIBTheoryAtom>> formulas,
        final SMTLogic logic,
        final Abortion aborter) throws AbortionException, WrongLogicException {
        final SMTLIBFormulaOutputVisitor vis = SMTFormulaToSMTLIBVisitor.create(logic);
        for (final Formula<SMTLIBTheoryAtom> f : formulas) {
            vis.handleConstraint(f);
        }
        // Retrieve old names for the variables and functions
        final Pair<YNM, Map<String, String>> resultPair = this.solve(vis.getResult(), logic, aborter);

        resultPair.y = SMTEngine.translateResultMapToOldNames(resultPair.y, vis.getVarNameMap());

        return resultPair;
    }

    /* (non-Javadoc)
     * @see aprove.solver.Engines.SMTEngine#solve(java.lang.String, aprove.solver.Engines.SMTEngine.SMTLogic, aprove.strategies.Abortions.Abortion)
     */
    /**
     * The current implementation passes AProVE's data structures for
     * SMT formulae to SMTInterpol via an SMTLIB2-compliant string and
     * the parser in SMTInterpol and also received the answer in an
     * SMTLIB2 String. Advantage: Does not require code modifications
     * in SMTInterpol, and the development time is slightly reduced.
     *
     * TODO for performance: pass the SMT formula to SMTInterpol via
     * its dedicated API methods, without the detour over serialization
     * and deserialization for an SMTLIB2 representation and also the
     * result output.
     */
    @Override
    public Pair<YNM, Map<String, String>> solve(final String smtString, final SMTLogic logic, final Abortion aborter)
            throws AbortionException, WrongLogicException {
        aborter.checkAbortion();

        // * pre-process smtString ...
        final String preprocessedSmtString =
            smtString.replace("(set-logic",
                "(set-option :produce-assignments true)\n(set-option :produce-models true)\n(set-logic");
        SMTInterpolEngine.LOG.finest(preprocessedSmtString);

        // * create a solver object
        final org.apache.log4j.Logger log4jLogger = org.apache.log4j.Logger.getRootLogger();
        log4jLogger.setLevel(org.apache.log4j.Level.WARN);
        final TerminationRequest termRequest = new AbortionTerminationRequest(aborter);
        final Script solver = new SMTInterpol(log4jLogger, termRequest);

        // * feed it with smtString
        final StringWriter stringWriter = new StringWriter(); // the unparsed answer will go here
        final PrintWriter resultSMTInterpolWriter = new PrintWriter(stringWriter);
        final ParseEnvironment parseEnvironment = new ParseEnvironment(solver);
        parseEnvironment.setOutStream(resultSMTInterpolWriter);
        final Reader smtStringReader = new StringReader(preprocessedSmtString);
        SMTInterpolEngine.LOG.fine("About to invoke SMTInterpol (same JVM, but via detour over a SMTLIB2 string) ...\n");
        final long nanos1 = System.nanoTime();

        // * ask the solver and hopefully receive an answer
        parseEnvironment.parseStream(smtStringReader, "AProVE!");
        final long nanos2 = System.nanoTime();
        SMTInterpolEngine.LOG.fine("SMTInterpol needed " + (nanos2 - nanos1) / 1000000 + " ms.\n");

        String answer = stringWriter.toString();
        answer = answer.replaceAll("Int\n   ", "Int").replaceAll("Bool\n   ", "Bool");
        SMTInterpolEngine.LOG.finest("SMTInterpol sez (after massaging):\n");
        SMTInterpolEngine.LOG.finest(answer);
        final String[] answerLinesArray = answer.split("\n");
        final List<String> answerLines = Arrays.asList(answerLinesArray);

        final Map<String, String> resMap = new LinkedHashMap<String, String>();

        // The below code has quite shamelessly been stolen from SMTLIBEngine.
        YNM resType = null;
        final Iterator<String> it = answerLines.iterator();
        while (it.hasNext()) {
            final String line = it.next();
            aborter.checkAbortion();
            SMTInterpolEngine.LOG.log(Level.FINEST, "{0}\n", line);
            if (line.startsWith("unsat")) {
                assert (resType == null) : "Got two answers from SMT solver!";
                SMTInterpolEngine.LOG.log(Level.FINE, "SMT solver says: UNSAT\n");
                resType = YNM.NO;
            } else if (line.startsWith("sat")) {
                assert (resType == null) : "Got two answers from SMT solver!";
                SMTInterpolEngine.LOG.log(Level.FINE, "SMT solver says: SAT\n");
                resType = YNM.YES;
            } else if (line.startsWith("unknown")) {
                assert (resType == null) : "Got two answers from SMT solver!";
                SMTInterpolEngine.LOG.log(Level.FINE, "SMT solver says: UNKNOWN\n");
                resType = YNM.MAYBE;
            } else if (line.startsWith("(define (")) {
                //Function definition, unhandled.
            } else if (line.startsWith("(define ")) {
                // Variable result: (define x 1)
                final String[] sArr = line.split(" ");
                // sArr[0] = "(define", [1] is var name, [2] is value + ")"
                assert (sArr.length == 3) : "Cannot parse SMT solver answer: " + line;
                if (sArr[2].endsWith("\"))")) {
                    resMap.put(sArr[1], sArr[2].substring(0, sArr[2].length() - 4));
                } else {
                    resMap.put(sArr[1], sArr[2].substring(0, sArr[2].length() - 1));
                }
            } else if (line.trim().startsWith("(define-fun")) {
                String completeLine;
                if (!line.endsWith(")")) {
                    assert (it.hasNext()) : "Expected more lines, only got '" + line + "'";
                    completeLine = line + " " + it.next();
                } else {
                    completeLine = line;
                }
                // Variable result: (define-fun x () Int 0)
                final String[] sArr = completeLine.trim().split("[ \t]+");
                if (sArr[3].equals("Bool")) { // only numbers, please
                    continue;
                }
                // sArr[0] = "(define-fun", [1] is var name, [2] () [3] Int [4] is value + ")"
                assert (sArr.length == 5 || sArr.length == 6 && sArr[2].equals("()") && sArr[3].equals("Int")) : "Cannot parse SMT solver answer: "
                    + completeLine;
                if (sArr.length == 6) {
                    assert sArr[4].equals("(-") : "Cannot parse SMT solver answer: " + completeLine;
                    if (sArr[5].endsWith("))")) {
                        resMap.put(sArr[1], sArr[4].substring(0, sArr[4].length() - 3)); // ")))"
                    } else {
                        resMap.put(sArr[1], sArr[4].substring(0, sArr[4].length() - 2)); // "))"
                    }
                } else {
                    if (sArr[4].endsWith("))")) {
                        resMap.put(sArr[1], sArr[4].substring(0, sArr[4].length() - 2)); // "))"
                    } else {
                        resMap.put(sArr[1], sArr[4].substring(0, sArr[4].length() - 1)); // ")"
                    }
                }
            } else {
                //Unknown line, try to ignore.
            }
        }
        SMTInterpolEngine.LOG.finer(resMap + "\n");

        aborter.checkAbortion();
        // * Yay, done!
        return new Pair<>(resType, resMap);
    }

    /**
     * Most shamelessly taken from SMTLIBEngine.
     *
     * @param formulas
     * @param logic
     * @param aborter
     * @return
     * @throws AbortionException
     * @throws WrongLogicException
     */
    public YNM solveAndPutIntoFormula(final List<Formula<SMTLIBTheoryAtom>> formulas,
        final SMTLogic logic,
        final Abortion aborter) throws AbortionException, WrongLogicException {
        final SMTLIBFormulaOutputVisitor vis = SMTFormulaToSMTLIBVisitor.create(logic);

        for (final Formula<SMTLIBTheoryAtom> f : formulas) {
            vis.handleConstraint(f);
        }
        // Retrieve old names for the variables and functions
        final Pair<YNM, Map<String, String>> resultPair = this.solve(vis.getResult(), logic, aborter);
        if (resultPair == null) {
            // WOOOOOWWW if THAT happens, there is something seriously wrong (like no more MEM)
            return YNM.MAYBE;
        }

        final YNM resType = resultPair.x;
        final Map<String, String> result = resultPair.y;
        if (result == null) {
            assert (resType != YNM.YES) : "SMT returned SAT, but we have no model!";
            return resType;
        }
        final SMTLIBVarNameMap varNameMap = vis.getVarNameMap();
        final Map<String, SMTLIBAssignableSemantics> nameToVarMap = varNameMap.getNameToVarMap();
        for (final Map.Entry<String, String> e : result.entrySet()) {
            final String key = e.getKey();
            final String val = e.getValue();

            if (key.startsWith("(")) {
                // Function value
                final SMTLIBFunction<?> v = (SMTLIBFunction<?>) nameToVarMap.get(key);
                if (v != null) {
                    final String[] sArr = key.split(" ");
                    final List<String> params = new ArrayList<String>(sArr.length);
                    for (final String element : sArr) {
                        params.add(element);
                    }
                    v.setResult(params, val);
                }
            } else {
                // Variable value
                final SMTLIBVariable<?> v = (SMTLIBVariable<?>) nameToVarMap.get(key);
                if (v != null) {
                    v.setResult(val);
                }
            }
        }
        return resType;
    }
}
