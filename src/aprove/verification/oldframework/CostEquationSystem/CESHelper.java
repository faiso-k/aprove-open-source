package aprove.verification.oldframework.CostEquationSystem;

import java.io.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.regex.*;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.*;
import aprove.verification.complexity.CpxRntsProblem.Processors.*;
import aprove.verification.complexity.TruthValue.*;

/**
 * Helper methods useful for conversion to cost relations used by CoFloCo (and PUBS)
 *
 * @author matt
 *
 */
public abstract class CESHelper {

    // run cofloco with output redirected to file (fast: improve performance, risk less precise bounds)
    // if output is written to a buffer and the buffer is full, CoFloCo stops executing. So don't use buffer
    public static List<String> executeCoFloCo(String input, int timeout, boolean fast, boolean assumeSequential, Abortion aborter) {
        return executeCoFloCoInternal(input, timeout, fast, assumeSequential, aborter);
    }

    // returns null if cofloco could not be started; timeout 0 means no timeout
    private static List<String> executeCoFloCoInternal(String input, int timeout, boolean fast, boolean assumeSequential, Abortion aborter) {
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
            List<String> parameters = new ArrayList<>();
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

            if (assumeSequential) {
                parameters.add("-assume_sequential");
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
            Reader outputReader = new FileReader(outfile);

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
            if (process != null) {
                process.destroyForcibly();
            }
            ex.printStackTrace();
            return null;
        } catch (ThreadDeath td) {
            if (process != null) {
                process.destroyForcibly();
            }
            throw td;
        } finally {
            if (process != null) {
                process.destroyForcibly();
            }
        }
    }

    //returns null if not found
    public static String obtainAsymptoticCoflocoResult(List<String> output) {
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

    public static ComplexityValue parseComplexity(String cpx) {
        String trimmed = cpx.trim();
        if (trimmed.equals("infinity")) {
            return ComplexityValue.infinite();
        }
        if (trimmed.equals("constant")) {
            return ComplexityValue.constant();
        }
        return KoATParser.parse(cpx);
    }

    //returns null if not found
    public static String obtainConcreteCoFloCoResult(List<String> output) {
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

    public static List<String> executePUBS(String input, int timeout, Abortion aborter) {
        try {
            // create input file
            File file = File.createTempFile("aprove", ".pubs");
            file.deleteOnExit();
            // write ITS to input file
            Writer inputWriter = new OutputStreamWriter(new FileOutputStream(file));
            inputWriter.write(input);
            inputWriter.close();
            // construct the invocation
            List<String> parameters = new ArrayList<>();
            parameters.add("pubs_static");
            parameters.add("-file");
            parameters.add(file.getCanonicalPath());
            // start the process
            ProcessBuilder processBuilder = new ProcessBuilder(parameters.toArray(new String[parameters.size()]));
            processBuilder.redirectErrorStream(true);
            Process process = processBuilder.start();
            TrackerFactory.process(aborter, process);
            // wait with timeout (and possibly kill process)
            if (timeout == 0) {
                process.waitFor();
            } else if (!process.waitFor(timeout, TimeUnit.MILLISECONDS)) {
                process.destroyForcibly();
                return null;
            }
            // read the output
            List<String> proofText = new LinkedList<>();
            try (BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()))) {
                for (String line = reader.readLine(); line != null; line = reader.readLine()) {
                    proofText.add(line);
                }
            } catch (IOException e) {
                //ignore (most probably we got killed by a timeout)
            }
            // done
            return proofText;
        } catch (IOException | InterruptedException ex) {
            ex.printStackTrace();
            return null;
        }
    }

    public static String obtainConcretePUBSResult(List<String> output) {
        String result = null;
        for (String line : output) {
            if (line.contains("Non Asymptotic Upper Bound:")) {
                Pattern p = Pattern.compile("Upper Bound:(.*)$");
                Matcher m = p.matcher(line);
                if (m.find()) {
                    result = m.group(1);
                    break;
                }
            }
        }
        if (result == null) {
            System.err.println("PUBS failed -- output was ");
            for (String line: output) {
                System.err.println(line);
            }
        }
        //check for PUBS failures
        if (result != null && (result.contains("c(maximize_failed)")
                || result.contains("c(failed("))) {
            result = null;
        }
        return result;
    }

    public static ComplexityValue getAsymptoticPUBSResult(String result) {
        if (result == null) {
            return ComplexityValue.infinite();
        }
        return PUBSParser.parse(result);
    }

}
