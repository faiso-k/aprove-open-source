package aprove.verification.complexity.CpxRntsProblem.Algorithms;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.Processors.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Helper methods useful for conversion to cost relations used by CoFloCo (and PUBS),
 * as well as methods to execute CoFloCo.
 *
 * @author mnaaf
 *
 */
public abstract class CoflocoHelper {

    private static Export_Util plainUtil = new PLAIN_Util();

    public static String exportConstraint(TRSTerm term) {
        if (term.equals(CpxIntTermHelper.TRUE)) {
            return "0 >= 0";
        } else if (term.equals(CpxIntTermHelper.FALSE)) {
            return "0 >= 1";
        }

        TRSFunctionApplication fun = (TRSFunctionApplication)term;
        FunctionSymbol f = fun.getRootSymbol();
        if (f.getArity() == 2) {
            String lhsString,rhsString;
            try {
                lhsString = CpxIntTermHelper.toSimplePolynomial(fun.getArgument(0)).export(plainUtil);
                rhsString = CpxIntTermHelper.toSimplePolynomial(fun.getArgument(1)).export(plainUtil);
            } catch (NotRepresentableAsPolynomialException e) {
                throw new RuntimeException("Export of nonpolynomial constraint " + fun + " to CoFloCo not supported!");
            }
            if (f.equals(CpxIntTermHelper.fLe)) {
                return lhsString + " =< " + rhsString;
            } else if (f.equals(CpxIntTermHelper.fLt)) {
                return lhsString + " < " + rhsString;
            } else if (f.equals(CpxIntTermHelper.fGe)) {
                return lhsString + " >= " + rhsString;
            } else if (f.equals(CpxIntTermHelper.fGt)) {
                return lhsString + " > " + rhsString;
            } else if (f.equals(CpxIntTermHelper.fEq)) {
                return lhsString + " = " + rhsString;
            }
        }
        System.err.println("Don't know how to export " + fun + " to CoFloCo for the constraint " + term);
        throw new RuntimeException("Export of constraint symbol " + f + " to CoFloCo not yet implemented!");
    }

    public static String exportTermSimple(TRSTerm term) {
        return IDPExport.exportTerm(term, plainUtil, IDPPredefinedMap.DEFAULT_MAP);
    }

    public static String exportFunapp(TRSFunctionApplication funapp, Optional<TRSVariable> errVar, TRSVariable retVar) {
        int extraArgs = errVar.isPresent() ? 2 : 1;
        FunctionSymbol fun = funapp.getRootSymbol();
        FunctionSymbol newFun = FunctionSymbol.create(fun.getName(), fun.getArity()+extraArgs);

        ArrayList<TRSTerm> newArgs = new ArrayList<>(funapp.getArguments());
        if (errVar.isPresent()) {
            newArgs.add(errVar.get());
        }
        newArgs.add(retVar);
        TRSTerm res = TRSTerm.createFunctionApplication(newFun, newArgs);
        return IDPExport.exportTerm(res, plainUtil, IDPPredefinedMap.DEFAULT_MAP);
    }

    public static String exportInputOutput(FunctionSymbol fun, List<TRSVariable> in, List<TRSVariable> out) {
        String inVars = in.stream().map(var -> var.getName()).collect(Collectors.joining(","));
        String outVars = out.stream().map(var -> var.getName()).collect(Collectors.joining(","));
        String res = "input_output_vars(" + fun.getName();
        if (!in.isEmpty() || !out.isEmpty()) res += "(";
        res += inVars;
        if (!in.isEmpty()) res += ",";
        res += outVars;
        if (!in.isEmpty() || !out.isEmpty()) res += ")";
        res += ",[" + inVars + "],[" + outVars + "]).";
        return res;
    }

    public static String exportCost(SimplePolynomial poly) {
        return IDPExport.exportTerm(poly.toTerm(), plainUtil, IDPPredefinedMap.DEFAULT_MAP);
    }

    // run cofloco with output redirected to file (fast: improve performance, risk less precise bounds)
    // if output is written to a buffer and the buffer is full, CoFloCo stops executing. So don't use buffer
    public static List<String> executeCoFloCo(String input, int timeout, boolean fast, Abortion aborter) {
        return executeCoFloCoInternal(input, timeout, fast, aborter);
    }

    // returns null if cofloco could not be started; timeout 0 means no timeout
    private static List<String> executeCoFloCoInternal(String input, int timeout, boolean fast, Abortion aborter) {
        Process process = null;
        try {
            // create input (and possibly output) file
            File file = File.createTempFile("aprove", ".ces");
            File outfile = null;
            outfile = File.createTempFile("aprove", ".out");
            file.deleteOnExit();

            // write ITS to input file
            Writer inputWriter = new OutputStreamWriter(new FileOutputStream(file));
            inputWriter.write(input);
            inputWriter.close();

            // construct the invocation
            List<String> parameters = new ArrayList<String>();
            parameters.add("cofloco");

            //do not compute lowerbounds (to increase performance)
            parameters.add("-compute_lbs");
            parameters.add("no");

            if (fast) {
                //trade performance vs. tight bounds (but asymptotic class should be the same)
                //options suggested by Antonio (author of CoFloCo)
                parameters.add("-compress_chains"); //merge similar execution patterns
                parameters.add("2");
                parameters.add("-solve_fast"); //greedy bound computation
            }

            parameters.add("-i");
            parameters.add(file.getCanonicalPath());

            // start the process
            ProcessBuilder processBuilder = new ProcessBuilder(parameters.toArray(new String[parameters.size()]));
            processBuilder.redirectErrorStream(true);
            processBuilder.redirectOutput(outfile);
            process = processBuilder.start();
            TrackerFactory.process(aborter, process);

            // wait with timeout (and possibly kill process)
            if (timeout == 0) {
                process.waitFor();
            } else if (!process.waitFor(timeout, TimeUnit.MILLISECONDS)) {
                process.destroyForcibly();
                return null;
            }

            //get the output
            Reader outputReader = null;
            outputReader = new FileReader(outfile);

            // read the output
            List<String> proofText = new LinkedList<>();
            try (BufferedReader reader = new BufferedReader(outputReader)) {
                for (String line = reader.readLine(); line != null; line = reader.readLine()) {
                    proofText.add(line);
                }
            } catch (IOException e) {
                //ignore (and possibly lose this result)
            }
            // done
            return proofText;
        } catch (IOException | InterruptedException ex) {
            ex.printStackTrace();
            return null;
        } finally {
            if (process != null) {
                process.destroyForcibly();
            }
        }
    }

    //returns null if not found
    public static String obtainAsymptoticResult(List<String> output) {
        for (String line : output) {
            if (line.contains("Asymptotic class:")) {
                Pattern p = Pattern.compile("Asymptotic class: (.*)$");
                Matcher m = p.matcher(line);
                if (m.find()) {
                    return m.group(1);
                }
            }
        }
        return null;
    }

    //returns null if not found
    public static String obtainConcreteResult(List<String> output) {
        for (String line : output) {
            if (line.contains("### Maximum cost of start")) {
                Pattern p = Pattern.compile("### Maximum cost of start[^:]*: (.*)$");
                Matcher m = p.matcher(line);
                if (m.find()) {
                    return m.group(1);
                }
            }
        }
        return null;
    }

    public static ComplexityValue parseComplexity(String cpx) {
        String trimmed = cpx.trim();
        if (trimmed.equals("infinity")) {
            return ComplexityValue.infinite();
        }
        if (trimmed.equals("constant")) {
            return ComplexityValue.constant();
        }
        return PUBSParser.parse(cpx);
    }

    public static SimplePolynomial parsePolynomial(String poly) throws NotRepresentableAsPolynomialException {
        String trimmed = poly.trim();
        if (trimmed.equals("infinity") || trimmed.equals("inf")) {
            throw new NotRepresentableAsPolynomialException();
        }
        return PUBSParser.parseAsPolynomial(poly);
    }

}
