package aprove.input.Programs.loat;

import java.io.*;
import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.processors.*;
import aprove.input.Programs.pushdownSMT.*;
import aprove.input.Programs.t2.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;
import aprove.verification.oldframework.SMT.Solver.Z3.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * 
 * This processor applies LoAT to the received obligation.
 * In theory, this processor can receive the oblogation of any of the three accepted input formats of Loat.
 * However, only the koat format is supported with witness generation.
 * 
 * LoAT can only prove non-termination. But it can not prove termination since it under-approximates the ITS. 
 * 
 * @author Constantin Mensendiek
 *
 */
public class LoATProcessor extends Processor.ProcessorSkeleton {
    
    private static class LoATExecutionException extends Exception {

        private static final long serialVersionUID = -594771260391616880L;

        public LoATExecutionException(String errorMessage, Throwable cause) {
            super(errorMessage, cause);
        }
    }

    /**
     * If true, errors when executing LoAT are printed to stderr
     */
    static final boolean PRINT_LOAT_ERRORS_TO_STDERR = true;

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof KoatProblem || obl instanceof SMTPushdownAutomaton || obl instanceof T2IntSys;
    }

    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        assert !Globals.useAssertions || obl instanceof KoatProblem || obl instanceof SMTPushdownAutomaton || obl instanceof T2IntSys;

        try {
            final File tempFile = writeToFile(obl);
            final List<String> loatCommand = determineLoatCommand(tempFile, aborter);

            Triple<Integer, List<String>, List<String>> loatOutput = ExecHelper.execAndGetExitCode(loatCommand,
                                                                                                   getEnv(),
                                                                                                   aborter);
            int loatExitCode = loatOutput.x;
            List<String> loatStdout = loatOutput.y;

            aborter.checkAbortion();

            if (loatExitCode != 0 && !aborter.isAborted()) {
                throw new LoATExecutionException("Running LoAT finished with non-zero exit code " + loatExitCode
                                                 + " when running command: \n"
                                                 + loatCommand + "\n" 
                                                 + "the error message is: \n"
                                                 + loatOutput.z,
                                                 null);
            }
            tempFile.delete();

            LoATProof loatProof = LoATProof.createFromOutput(loatCommand, loatStdout);
            String proofMessage = loatProof.message;
            switch (loatProof.status) {
                /* LoAT cannot prove termination
                case YES:
                    return ResultFactory.proved(loatProof);
                */
                case NO:
                    if(obl instanceof KoatProblem) {
                        Pair<String,String> witnessAndLog = generateWitness(obl, loatStdout, aborter);
                        LLVMWitness witness = new LLVMWitness(witnessAndLog.x);
                        loatProof.setWitness(witness);
                        loatProof.addLog(witnessAndLog.y);
                    }
                    return ResultFactory.disproved(loatProof);
                case MAYBE:
                    return ResultFactory.unknown(loatProof);
                default:
                    throw new IllegalArgumentException("Invalid YNM value " + loatProof.status);
            }

        } catch (LoATExecutionException e) {
            if (PRINT_LOAT_ERRORS_TO_STDERR) {
                System.err.println(e.getMessage());
            }
            return ResultFactory.error(e.getMessage());
        } catch (IOException | InterruptedException e) {
            // Build a string from the exception and return it as the error
            StringBuilder sb = new StringBuilder();
            sb.append("Unknown error running loat\n");
            sb.append(e.getMessage()).append("\n");
            for (StackTraceElement el : e.getStackTrace()) {
                sb.append(el.toString()).append("\n");
            }

            String errorMessage = sb.toString();
            System.err.println(errorMessage);
            return ResultFactory.error(errorMessage);
        }
    }

    private Pair<String,String> generateWitness(BasicObligation obl, List<String> output, Abortion aborter) {
        String log = "";
        if (this.witnessGeneration == WitnessGeneration.NO_WITNESS) {
            return new Pair<String,String>(null,log);
        }
        
        List<PlainIntegerRelation> guard = LoATOutputParser.finalGuard(output);
        log += "\n\nThe final guard is:\n";
        for (PlainIntegerRelation rel : guard) log+=rel.export(new PLAIN_Util())+";";
        
        Map<String, LLVMHeuristicConstRef> varAssignMap = new HashMap<>();
        Z3ExtSolverFactory factory = new Z3ExtSolverFactory();
        Z3Solver z3 = factory.getSMTSolver(SMTLIBLogic.QF_NIA, aborter);
        ArrayList<Symbol<?>> varSymbols = new ArrayList<>();
        // parse relation and give it to z3
        for (PlainIntegerRelation intRel : guard) {
            z3.addAssertion(intRel.toSMTExp());
            // collect variables to check their assignment later
            for (IntegerVariable var : intRel.getVariables()) {
                varSymbols.add((Symbol<?>) var.toSMTExp());
            }
        }
        // if a model is found, store an assignment from variables to constants in varAssignMap
        if (z3.checkSAT() == YNM.YES) {
            Optional<Model> m = z3.getModel();
            if (m.isPresent()) {
                Model model = m.get();
                for (Symbol<?> symbol : varSymbols) {
                    if (model.get(symbol) instanceof Call1) {
                        // for negative integer assignments
                        Call1 assignment = (Call1) model.get(symbol);
                        if (assignment.getSym().equals(Symbol1.IntsNegate)) {
                            varAssignMap.put(symbol.toString(), toConstRef(assignment.getA0(), true));
                        }
                    } else if (model.get(symbol) instanceof IntConstant) {
                        // for positive integer assignments
                        varAssignMap.put(symbol.toString(), toConstRef(model.get(symbol), false));
                    }
                }
                log += "\n\nZ3 found a model for the final guard:\n"+varAssignMap.toString();
            } else {
                log += "\n\nZ3 did not provide a model, although the guard is satisfiable.";
            }
        }
        
        String witness = null;
        switch(this.witnessGeneration) {
            case TRACKING_OF_VARIABLES:
                log += "\n\nTry to generate a witness via backtracking variable names:\n";
                witness = WitnessGenerationHelper.generateWitness(obl, varAssignMap, aborter);
                break;
            case RETRACING_SIMPLIFICATIONS:
                log += "\n\nTry to generate a witness via retracing LoAT's simplifications:\n";
                try {
                    witness = WitnessGenerationHelper.generateFunctionSymbolList(obl, varAssignMap, aborter, output);
                } catch(AssertionError e) {
                    //e.printStackTrace();
                    log += "  AssertionError: "+e.getMessage()+"\n";
                }
                break;
            default:
                break;
        }
        
        log += witness != null ? "Witness successfully generated" : "No witness generated";
        
        return new Pair<String,String> (witness,log);
    }

    /**
     * Convert a SMT expression to a LLVM constant
     *
     * @param expr     the SMT expression to be converted
     * @param negation true if the constant should be negated, false otherwise
     * @return the LLVM constant
     */
    private static LLVMHeuristicConstRef toConstRef(SMTExpression expr, boolean negation) {
        if (expr instanceof IntConstant) {
            BigInteger val = ((IntConstant) expr).getConstant();
            if (negation) {
                val = val.negate();
            }
            return new LLVMHeuristicConstRef(val);
        }

        throw new IllegalArgumentException("Input expression cannot be converted to an integer constant.");
    }
    
    /**
     * write any of the three obligations as their intended format into a temporary file
     * 
     * @param problem
     * @return
     * @throws IOException
     */
    private File writeToFile(BasicObligation problem) throws IOException {  
        String content = "";
        String fileSuffix = "";
        if (problem instanceof KoatProblem) {
            fileSuffix = ".koat";
            content = problem.export(new PLAIN_Util());
        } else if (problem instanceof T2IntSys){
            fileSuffix = ".t2";
            content = problem.export(new PLAIN_Util());
        } else if (problem instanceof SMTPushdownAutomaton){
            fileSuffix = ".smt2";
            content = problem.export(new PLAIN_Util());
            // dirty trick to solve the following problem: loat crashes when the smt2 contains 'false'
            content = content.replaceAll("false", "(= 0 1)");
        }
        final File tempFile = File.createTempFile("aprove.input.Programs.loat", fileSuffix);
        final OutputStream os = new FileOutputStream(tempFile);
        final Writer fileWriter = new OutputStreamWriter(os);        
        fileWriter.write(content);
        fileWriter.close();
        return tempFile;
    }
    

    /**
     * this function specifies the command LoAT is called with. 
     * 
     * @param file
     * @param aborter
     * @return
     * @throws LoATExecutionException
     * @throws InterruptedException
     */
    private List<String> determineLoatCommand(File file, Abortion aborter) throws LoATExecutionException,
                                                                              InterruptedException {
        List<String> res = new ArrayList<>();

        // determine the loat file given by the variable LOAT_PATH
        String loatPathStr = System.getenv("LOAT_PATH");
        String errorMsg =
                        "Set the 'LOAT_PATH' environment variable to point to the folder containing the executable loat file";
        String linebreak = System.lineSeparator();
        if (loatPathStr == null) {
            throw new LoATExecutionException("No LoAT installation found. " + linebreak + errorMsg, null);
        }
        File loatPath = new File(loatPathStr);
        if (!loatPath.exists() || !loatPath.isDirectory() || !loatPath.canRead()) {
            throw new LoATExecutionException("LOAT_PATH isn't a readable directory.", null);
        }
        List<String> files = Arrays.asList(loatPath.list());
        if (!files.contains("loat")) {
            throw new LoATExecutionException("No loat found. " + linebreak + errorMsg, null);
        }

        res.add(loatPath.getAbsolutePath() + File.separator + "loat");

        // test the executable loat file
        try {
            ExecHelper.execAndGetExitCode(res, getEnv(), aborter);
        } catch (IOException e) {
            throw new LoATExecutionException("Unable to launch loat with command: \n" + res
                                             + "\nUnderlying IOException: "
                                             + e.getMessage(),
                                             e);
        }

        // disable colored output
        res.add("--plain");
        // only try to prove nontermination
        res.add("--nonterm");
        // loat needs to do preprocessing for smt2 input to run consistently 
        // res.add("--no-preprocessing");
        // output only complexity or 'NO' for nontermination
        res.add("--proof-level");
        res.add("3");
        // path to temporary file 
        res.add(file.getAbsolutePath());
        return res;
    }

    private Map<String, String> getEnv() {
        Map<String, String> env = new HashMap<>();
        env.put("PATH", System.getenv("PATH"));
        return env;
    }
    
    /**
     * parameter that specifies how/if the witness is generated
     */
    private final WitnessGeneration witnessGeneration;

    /**
     * @param arguments The parameters of this processor.
     */
    @ParamsViaArgumentObject
    public LoATProcessor(LoATProcessor.Arguments arguments) {
        this.witnessGeneration = arguments.witnessGeneration;
    }

    public static class Arguments {
        public WitnessGeneration witnessGeneration =
                Globals.generateGraphmlWitness ? WitnessGeneration.RETRACING_SIMPLIFICATIONS : WitnessGeneration.NO_WITNESS;
    }
    
    public enum WitnessGeneration {
        /**
         * generate the witness by backtracking the variables via their renaming 
         */
        TRACKING_OF_VARIABLES,
        /**
         * generate the witness by parsing the output of LoAT 
         * which includes a detailed instruction of the chaining and acceleration to get the nonterminating path
         */
        RETRACING_SIMPLIFICATIONS,
        /**
         * do not generate a witness
         */
        NO_WITNESS
    }

    public static class LoATProof extends DefaultProof implements HasGraphmlWitness {

        private String message;
        private LLVMWitness witness;
        private YNM status;

        /**
         * Constructor for LoAT proof result
         *
         * @param message proof message printed by LoAT
         * @param status  proof status
         * @param graphmlWitness GraphML witness
         */
        private LoATProof(final String message, YNM status) {
            this.shortName = "LoAT";
            this.longName = "Proof by Loop Accelation (LoAT)";
            this.message = message;
            this.status = status;
        }

        public void addLog(String log) {
            this.message += log;
        }

        static LoATProof createFromOutput(List<String> command, List<String> output) {
            StringBuilder proofBuilder = new StringBuilder();
            
            proofBuilder.append("LoAT was called with the following command:\n\n");
            for (String c : command) {
                proofBuilder.append(c).append(" ");
            }
            proofBuilder.append("\n\n").append("LoAT's output was:\n\n");
            
            YNM conclusion = YNM.MAYBE;
            if (output.get(output.size() - 1).equals("NO")) {
                conclusion = YNM.NO;
            }

            Queue<String> loatStdout = new LinkedList<>(output);

            do {
                String currentLine = loatStdout.poll();
                proofBuilder.append(currentLine).append('\n');
            } while (!loatStdout.isEmpty());

            String proofString = proofBuilder.toString();
            if (proofString.isEmpty()) {
                proofString = "No proof given by LoAT";
            }

            return new LoATProof(proofString, conclusion);
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o instanceof HTML_Util ? o.export("<pre style=\"overflow-y:scroll\">" + message + "</pre>")
                                          : o.export(message);
        }
        
        public String getGraphmlWitness() {
            return this.witness.getGraphmlWitness();
        }
        
        public void setWitness(LLVMWitness graphmlWitness) {
            this.witness = graphmlWitness;
        }
    }
}
