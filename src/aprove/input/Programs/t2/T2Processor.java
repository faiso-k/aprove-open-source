package aprove.input.Programs.t2;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.processors.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntTRS.*;
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

import java.io.*;
import java.math.BigInteger;
import java.util.*;

/**
 * Runs T2 on a T2IntSys. If T2 was not able to provide a proof, the processor
 * tries to under-approximate the T2IntSys and find a nontermination proof
 * based on the under-approximated version
 * <p>
 * The processor can be configured with two environment variables:
 * <ul>
 * <li><code>T2_PATH</code>: A fully qualified path to <code>T2.exe</code>
 * <li><code>MONO_PATH</code> (optional): A fully qualified path pointing
 * to the mono executable. If nothing is specified <code>$PATH</code>
 * is used to find mono
 * </ul>
 *
 * @author Alex Hoppen
 * @author Jera Hensel
 * @author Jiong Fu
 */
public class T2Processor extends Processor.ProcessorSkeleton {

    private static class T2ExecutionException extends Exception {
        private static final long serialVersionUID = -6079580015872965779L;

        public T2ExecutionException(String errorMessage, Throwable cause) {
            super(errorMessage, cause);
        }
    }

    /**
     * Unfold constant multiplications of the form c*v with c <= UNFOLD_CONST_MULT_UP_TO
     * to v + v + ... + v
     */
    static final int UNFOLD_CONST_MULT_UP_TO = 50;

    /**
     * If true, errors when executing T2 are printed to stderr
     */
    static final boolean PRINT_T2_ERRORS_TO_STDERR = true;

    // Debug flags
    static final boolean DUMP_T2_IRS = false;
    static final boolean DUMP_T2_OUTPUT = false;

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof T2IntSys;
    }

    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        assert !Globals.useAssertions || obl instanceof T2IntSys;

        T2IntSys problem = (T2IntSys) obl;

        if (UNFOLD_CONST_MULT_UP_TO > 0) {
            problem = problem.unfoldConstantMultiplication(UNFOLD_CONST_MULT_UP_TO);
        }

        try {
            if (DUMP_T2_IRS) {
                System.out.println(problem.export(new PLAIN_Util()));
            }

            final File tempT2File = writeT2IntSysToFile(problem);
            final List<String> t2Command = determineT2Command(tempT2File, aborter);

            Triple<Integer, List<String>, List<String>> t2Output = ExecHelper.execAndGetExitCode(t2Command, getEnv(), aborter);
            int t2ExitCode = t2Output.x;
            List<String> t2Stdout = t2Output.y;

            aborter.checkAbortion();

            if (t2ExitCode != 0 && !aborter.isAborted()) {
                throw new T2ExecutionException("Running T2 finished with non-zero exit code " + t2ExitCode + " when running command: \n" + t2Command, null);
            }
            tempT2File.delete();

            T2Proof t2Proof = T2Proof.createFromOutput(t2Stdout, aborter);
            String proofMessage = t2Proof.message;
            switch (t2Proof.status) {
                case YES:
                    return ResultFactory.proved(t2Proof);
                case NO:
                    LLVMWitness witness;
                    if (Globals.generateGraphmlWitness) {
                        witness = new LLVMWitness(generateWitness(obl, t2Proof.varAssignMap, aborter));
                    } else {
                        witness = new LLVMWitness("");
                    }
                    t2Proof.setWitness(witness);

                    return ResultFactory.disproved(t2Proof);
                case MAYBE:
                    // If the problem is already an under-approximation, we could not prove termination
                    // If not, try to under-approximate the T2IntSys and run T2 again.
                    if (problem.isUnderapproximation()) {
                        return ResultFactory.unsuccessful(proofMessage);
                    } else {
                        Map<Integer, List<T2IntTransGuard>> addedGuards = new HashMap<>();
                        T2IntSys underapproximation = problem.underapproximate(addedGuards);
                        assert !Globals.useAssertions || underapproximation.isUnderapproximation();

                        return ResultFactory.proved(underapproximation, YNMImplication.COMPLETE, new T2UnderapproximationProof(addedGuards));
                    }
                default:
                    throw new IllegalArgumentException("Invalid YNM value " + t2Proof.status);
            }

        } catch (T2ExecutionException e) {
            if (PRINT_T2_ERRORS_TO_STDERR) {
                System.err.println(e.getMessage());
            }
            return ResultFactory.error(e.getMessage());
        } catch (IOException | InterruptedException e) {
            // Build a string from the exception and return it as the error
            StringBuilder sb = new StringBuilder();
            sb.append("Unknown error running T2\n");
            sb.append(e.getMessage()).append("\n");
            for (StackTraceElement el : e.getStackTrace()) {
                sb.append(el.toString()).append("\n");
            }

            String errorMessage = sb.toString();

            if (PRINT_T2_ERRORS_TO_STDERR) {
                System.err.println(errorMessage);
            }

            return ResultFactory.error(errorMessage);
        }
    }

    /**
     * Get the lasso problem of the current termination problem
     *
     * @param currentProblem the current termination problem
     * @return the lasso problem of the current termination problem if the lasso problem is found, null otherwise
     */
    private static BasicObligation getGraphProblem(BasicObligation currentProblem) {
        BasicObligation currentObligation = currentProblem;

        while (currentObligation.getParent() != null) {
            if (currentObligation instanceof LLVMLassoProblem || currentObligation instanceof LLVMSEGraphProblem) {
                return currentObligation;
            }
            currentObligation = currentObligation.getParent();
        }

        return null;
    }

    /**
     * Get the variable assignment in lasso problem for the current termination problem
     *
     * @param currentProblem the current termination problem
     * @param varAssign the variable assignment in current termination problem
     * @return the variable assignment in lasso problem
     */
    private static Map<String, LLVMHeuristicConstRef> getLassoVariableAssignment(BasicObligation currentProblem, Map<String, LLVMHeuristicConstRef> varAssign) {
        Map<String, LLVMHeuristicConstRef> resultVarAssign = new HashMap<>();

        varAssign.forEach((key, value) -> {
            getLassoVariables(currentProblem, key)
                    .forEach(originalVar -> resultVarAssign.put(originalVar, value));
        });

        return resultVarAssign;
    }

    /**
     * Get the variables in lasso problem for the current termination problem
     *
     * @param currentProblem  the current termination problem
     * @param currentVariable the variable in current termination problem
     * @return the variables in lasso problem
     */
    private static List<String> getLassoVariables(BasicObligation currentProblem, String currentVariable) {
        if (currentProblem == null) {
            throw new IllegalArgumentException("Current problem cannot be null.");
        }

        BasicObligation currentObligation = currentProblem;
        List<String> foundKeyPre = new LinkedList<>(); // keys found in the previous round
        List<String> foundKeyPost = new LinkedList<>(); // keys found in the current round according to the keys found in the previous round
        foundKeyPre.add(currentVariable);

        do {
            // if current obligation contains variable renaming, get the key according to the value
            if (currentObligation instanceof VariableRenaming) {
                ((VariableRenaming) currentObligation).getVariableRenaming()
                        .forEach((key, value) -> {
                            foundKeyPre.forEach(keyPre -> {

                                // if the key is found in the current round, add it to the post list
                                if (value.contains(keyPre)) {
                                    foundKeyPost.add(key);
                                }

                            });
                        });
                // if a key from the previous round is not found after iterating over the current variable renaming,
                // it means the variable renaming from that key only happens in the previous round
                // and the back tracking of that key is omitted in the current round

                // move the keys in post list to pre list
                foundKeyPre.clear();
                foundKeyPre.addAll(foundKeyPost);
                foundKeyPost.clear();
            }

            // if the target problem is reached, return the result directly
            // if the the current obligation is not a lasso but the parent is a graph, a strategy is used where the whole graph is transformed to an ITS
            if (currentObligation.getClass() == LLVMLassoProblem.class || currentObligation.getParent() instanceof LLVMSEGraphProblem) {
                return foundKeyPre;
            }

            currentObligation = currentObligation.getParent();
        } while (currentObligation != null);
        return foundKeyPre;
    }

    /**
     * Get environment variables as key-value pair
     *
     * @return environment variables as key-value pair
     */
    private Map<String, String> getEnv() {
        File t2Path = new File(System.getenv("T2_PATH"));
        Map<String, String> env = new HashMap<>();
        env.put("LD_LIBRARY_PATH", t2Path.getAbsolutePath());
        // make windows users happy
        env.put("PATH", t2Path.getAbsolutePath() + ":" + System.getenv("PATH"));
        return env;
    }

    private String generateWitness(BasicObligation obligation, Map<String, LLVMHeuristicConstRef> varAssign, Abortion aborter) {
        // if no variable assignment in lasso is found, stop generating immediately
        if (varAssign == null || varAssign.isEmpty()) {
            return GraphMLWitnessBuilder.buildEmptyGraphMLWitness();
        }

        BasicObligation graphProblem = getGraphProblem(obligation);
        if (graphProblem != null) {
            Map<String, LLVMHeuristicConstRef> lassoVarAssign = getLassoVariableAssignment(obligation, varAssign);
            if (graphProblem instanceof LLVMLassoProblem) {
                return ((LLVMLassoProblem)graphProblem).buildGraphMLWitness(lassoVarAssign, aborter);
            } else if (graphProblem instanceof LLVMSEGraphProblem) {
                return ((LLVMSEGraphProblem)graphProblem).buildGraphMLWitness(lassoVarAssign, aborter);
            }
        }

        // TODO build witness when getLassoProblem(obl) is an IRSProblem (so there is no graph/lasso)
        return GraphMLWitnessBuilder.buildEmptyGraphMLWitness();
    }

    private File writeT2IntSysToFile(T2IntSys problem) throws IOException {
        final File tempT2File = File.createTempFile("aprove.input.Programs.t2", ".t2");
        final OutputStream t2OS = new FileOutputStream(tempT2File);
        final Writer t2FileWriter = new OutputStreamWriter(t2OS);
        t2FileWriter.write(problem.export(new PLAIN_Util()));
        t2FileWriter.close();
        return tempT2File;
    }

    private List<String> determineT2Command(File t2File, Abortion aborter) throws InterruptedException, T2ExecutionException {
        String monoPath = System.getenv("MONO_PATH");
        if (monoPath == null) {
            monoPath = "mono";
        }

        String t2PathStr = System.getenv("T2_PATH");
        String errorMsg = "Set the 'T2_PATH' environment variable to point to the folder containing T2.exe and libz3.so / libz3.dll / libz3.dylib";
        String linebreak = System.lineSeparator();
        if (t2PathStr == null) {
            throw new T2ExecutionException("No T2 installation found. " + linebreak + errorMsg, null);
        }
        File t2Path = new File(t2PathStr);
        if (!t2Path.exists() || !t2Path.isDirectory() || !t2Path.canRead()) {
            throw new T2ExecutionException("T2_PATH isn't a readable directory.", null);
        }
        List<String> files = Arrays.asList(t2Path.list());
        if (!files.contains("T2.exe")) {
            throw new T2ExecutionException("No T2.exe found. " + linebreak + errorMsg, null);
        }
        if (files.stream().noneMatch(x -> x.startsWith("libz3."))) {
            throw new T2ExecutionException("No libz3.so / libz3.dll / libz3.dylib found. " + linebreak + errorMsg, null);
        }

        // Whether the version of t2 is old and requires arguments with single dash only
        final boolean oldT2Version;

        // Execute T2 without any parameters to guess version and arguments
        List<String> res = new ArrayList<>();
        res.add(monoPath);
        res.add(t2Path.getAbsolutePath() + File.separator + "T2.exe");
        try {
            Triple<Integer, List<String>, List<String>> t2Output = ExecHelper.execAndGetExitCode(res, getEnv(), aborter);
            oldT2Version = t2Output.y.size() > 0 && t2Output.y.get(0).startsWith("T2 program prover/analysis tool.");
        } catch (IOException e) {
            throw new T2ExecutionException("Unable to launch T2 with command: \n" + res + "\nUnderlying IOException: " + e.getMessage(), e);
        }

        if (oldT2Version) {
            res.add("-try_nonterm");
            res.add("1");
            res.add("-print_proof");
            res.add("-termination");
            res.add("-input_t2");
        } else {
            res.add("--try_nonterm=1");
            res.add("--print_proof");
            res.add("--termination");
        }
        res.add(t2File.getAbsolutePath());
        return res;
    }

    public class T2UnderapproximationProof extends DefaultProof {
        /**
         * The guard statements that were added while under-approximating
         */
        private final Map<Integer, List<T2IntTransGuard>> addedGuards;

        /**
         * Create the proof.
         */
        T2UnderapproximationProof(final Map<Integer, List<T2IntTransGuard>> addedGuards) {
            this.shortName = "T2 Underapproximation";
            this.longName = "Proof for the under-approximation of an T2 IntSys";
            this.addedGuards = addedGuards;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("Added the following guard statements:");
            sb.append(o.newline());
            sb.append(o.newline());
            for (Map.Entry<Integer, List<T2IntTransGuard>> entry : addedGuards.entrySet()) {
                sb.append("Transition ");
                sb.append(entry.getKey());
                sb.append(":");
                for (T2IntTransGuard guard : entry.getValue()) {
                    sb.append(o.linebreak());
                    sb.append(o.preFormatted(guard.toString()));
                }
                sb.append(o.newline());
            }
            return sb.toString();
        }
    }

    public static class T2Proof extends DefaultProof implements HasGraphmlWitness {
        private final String message;
        private final Map<String, LLVMHeuristicConstRef> varAssignMap = new HashMap<>();
        private YNM status;
        private LLVMWitness witness;

        /**
         * Constructor for T2 proof result
         *
         * @param message proof message printed by T2
         * @param status  proof status
         */
        private T2Proof(final String message, YNM status) {
            this.shortName = "T2";
            this.longName = "Proof by the T2 tool";
            this.message = message;
            this.status = status;
        }

        static T2Proof createFromOutput(List<String> output, Abortion aborter) {
            Queue<String> t2Stdout = new LinkedList<>(output);
            StringBuilder proofBuilder = new StringBuilder();
            Map<String, LLVMHeuristicConstRef> varAssignMap = new HashMap<>();
            YNM conclusion = YNM.MAYBE;

            do {
                String currentLine = t2Stdout.poll();
                proofBuilder.append(currentLine).append('\n');
                if (currentLine != null) {
                    if (currentLine.startsWith("Nontermination proof succeeded")) {
                        conclusion = YNM.NO;
                    } else if (currentLine.startsWith("Termination proof succeeded")) {
                        conclusion = YNM.YES;
                    } else if (currentLine.startsWith("Found this recurrent set")) {
                        String varAssignsStr = currentLine.split(":")[1].trim();
                        String[] relations = varAssignsStr.split("and");
                        Z3ExtSolverFactory factory = new Z3ExtSolverFactory();
                        Z3Solver z3 = factory.getSMTSolver(SMTLIBLogic.QF_NIA, aborter);
                        ArrayList<Symbol<?>> varSymbols = new ArrayList<>();
                        // parse relation and give it to z3
                        for (String rel : relations) {
                            PlainIntegerRelation intRel = intRelationOf(rel);
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
                            }
                        }
                    }
                }
            } while (!t2Stdout.isEmpty());

            String proofString = proofBuilder.toString();
            if (proofString.isEmpty()) {
                proofString = "No proof given by T2";
            }

            T2Proof t2Proof = new T2Proof(proofString, conclusion);
            t2Proof.varAssignMap.putAll(varAssignMap);
            return t2Proof;
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

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o instanceof HTML_Util ? o.export("<pre style=\"overflow-y:scroll\">" + message + "</pre>") : o.export(message);
        }

        @Override
        public String getGraphmlWitness() {
            return this.witness.getGraphmlWitness();
        }

        /**
         * Convert the input string to an integer relation recognized by Z3
         *
         * @param input the input string to be converted
         * @return the relation recognized by Z3
         */
        private static PlainIntegerRelation intRelationOf(String input) {
            String[] operands;
            IntegerRelationType relationType;

            if (input.contains("==")) {
                relationType = IntegerRelationType.EQ;
                operands = input.split("==");
            } else if (input.contains(">=")) {
                relationType = IntegerRelationType.GE;
                operands = input.split(">=");
            } else if (input.contains("<=")) {
                relationType = IntegerRelationType.LE;
                operands = input.split("<=");
            } else if (input.contains(">")) {
                relationType = IntegerRelationType.GT;
                operands = input.split(">");
            } else if (input.contains("<")) {
                relationType = IntegerRelationType.LT;
                operands = input.split("<");
            } else {
                throw new IllegalArgumentException("String relation cannot be parsed for further process, since relation type cannot be recognized.");
            }

            if (operands.length != 2) {
                throw new IllegalStateException("String relation cannot be parsed for further process.");
            }

            FunctionalIntegerExpression lhs = intExpressionOf(operands[0].trim());
            FunctionalIntegerExpression rhs = intExpressionOf(operands[1].trim());
            return new PlainIntegerRelation(relationType, lhs, rhs);
        }

        /**
         * Convert the input string to an integer expression recognized by Z3
         *
         * @param input the input string to be converted
         * @return the expression recognized by Z3
         */
        private static FunctionalIntegerExpression intExpressionOf(String input) {
            final String constRegExp = "-?\\d+";
            final String posVarRegExp = "[a-zA-Z_$]\\w+";
            final String negVarRegExp = "-[a-zA-Z_$]\\w+";
            final String varRegExp = "-?[a-zA-Z_$]\\w+";
            final String operatorExp = "[+\\-]";
            final String operationRegExp = String.format("((%s|%s)%s)+(%s|%s)", varRegExp, constRegExp, operatorExp, varRegExp, constRegExp);

            if (input.matches(constRegExp)) {
                // for a constant, instantiate PlainIntegerConstant object directly
                return new PlainIntegerConstant(new BigInteger(input));
            } else if (input.matches(posVarRegExp)) {
                // for a variable, instantiate PlainIntegerVariable object directly
                return new PlainIntegerVariable(input);
            } else if (input.matches(negVarRegExp)) {
                // for a negated variable, instantiate PlainIntegerOperation object for unary operator
                return new PlainIntegerOperation(ArithmeticOperationType.NEG, new PlainIntegerVariable(input.substring(1)));
            } else if (input.matches(operationRegExp)) {
                // for an operation, instantiate PlainIntegerOperation object for binary operator

                // get the maximum last index of operators and get rid of the leading negation
                int lastIndexOfPlus = input.lastIndexOf('+');
                int lastIndexOfMinus = input.lastIndexOf('-');
                int operatorIndex = Math.max(lastIndexOfPlus, lastIndexOfMinus);

                // if the operation contains an addition with a negated variable or a negative integer
                if (lastIndexOfPlus + 1 == lastIndexOfMinus) {
                    // then the addition should be treated as the operator
                    operatorIndex = lastIndexOfPlus;
                }

                // process the operator
                ArithmeticOperationType operationType = null;
                char operator = input.charAt(operatorIndex);
                switch (operator) {
                    case '+':
                        operationType = ArithmeticOperationType.ADD;
                        break;
                    case '-':
                        operationType = ArithmeticOperationType.SUB;
                        break;
                    default:
                        throw new IllegalStateException("Arithmetic operation type is not supported. " + operator);
                }

                // process the operands
                FunctionalIntegerExpression firstExpression = intExpressionOf(input.substring(0, operatorIndex));
                FunctionalIntegerExpression secondExpression = intExpressionOf(input.substring(operatorIndex + 1));
                return new PlainIntegerOperation(operationType, firstExpression, secondExpression);
            }

            throw new IllegalArgumentException("Input string cannot be converted to an expression. " + input);
        }
        
        public void setWitness(LLVMWitness witness) {
            this.witness = witness;
        }
    }

}
