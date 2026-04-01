package aprove.verification.dpframework;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.input.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotators.*;
import aprove.verification.oldframework.Input.TypeAnalyzers.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.ObligationFactories.*;


/**
 * @author swiste
 * This Processor calls an external program and transfers the the current obligation
 * to this program. There after the processor receives its result and transform it back to
 * obligations.
 *
 *
 * Protocol for the external program:
 * the call:
 *
 *    externalProgram KIND ARGS
 *
 * KIND is the file extension of the aprove input format
 * ARGS are the arguments given by the strategy program
 *
 * the external program will receive the obligation in aprove input format
 * like qdp form standard input per pipe
 *
 * then the external program should
 * answer per standard output in this format if its successful:
 *
 *    PROOF COMPLETE           // proof implications are COMPLETE, SOUND, EQUIVALENT
 *    ...                      // some textual descriptions of the proof
 *    END PROOF
 *    AND                      // obligation junctor (OR is also possible)
 *    OBLIGATION qdp           // first obligation with its aprove input format
 *    ...                        // the obligation code
 *    END OBLIGATION           // end of the obligation
 *    OBLIGATION qdp           // next obligation
 *    ...
 *    END OBLIGATION
 *    ...
 *    END                      // no more obligations (there may be no new obligations)
 *
 *
 *  or in this format if it fails to proof anything:
 *
 *    FAIL
 *    ...                      // some textual description of the reason for failing
 *    END
 *
 *
 * Optionally, you can prefix either of those with a block specifying a
 * strategy to use. For imperative programmers: This strategy will be executed
 * just before the ExternalProcessor returns. For functional programmers: The
 * ExternalProcessor will evaluate to this strategy.
 * This block is in the following format:
 *
 *    STRATEGY SIMPLE          // Currently supported: SIMPLE and PROGRAM
 *    ...                      // A definition of the new strategy (see below)
 *    END
 *
 * For SIMPLE, the strategy should be one line containing a single word, which
 * should be a strategy defined in the main strategy program. This offers little
 * flexibility, but should be quite fast.
 * For PROGRAM, the strategy should be in the same format as the main strategy
 * program, and define a "main" strategy, which will be executed. Note that any
 * heuristics processors called from here will see the strategies from the main
 * program and not from this string, which may cause odd behavior.
 * Other formats may be introduced in the future, e.g. to be able to reference
 * strategies defined in the regular strategy program.
 *
 *
 *  Result example (semantic free):
 *  1:
 *    PROOF SOUND
 *      proving everything
 *    END PROOF
 *    AND
 *    END
 *
 *  2:
 *    PROOF COMPLETE
 *      disproving everything
 *    END PROOF
 *    OR
 *    END
 *
 *  3:
 *    PROOF SOUND
 *      failing on everything
 *    END PROOF
 *    OR
 *    END
 *
 *  4:
 *    PROOF EQUIVALENT
 *       transformed to a qdp
 *    END PROOF
 *    AND
 *    OBLIGATION qdp
 *    (VAR x)
 *    (PAIRS f(x) -> x)
 *    (RULES )
 *    (Q )
 *    (NOT MINIMAL)
 *    END OBLIGATION
 *    END
 *
 *  5:
 *    STRATEGY SIMPLE
 *      workOnDPs
 *    END STRATEGY
 *    FAIL
 *      I'm just a heuristic
 *    END
 *
 *
 * Using the ExternalProcessor in a strategy program
 *
 *     External[Call = "program to call",
 *              Accepts = "kinds of obligations to accept",
 *              Args = "argumet1 argument2",
 *              ShortName = "short description",
 *              LongName = "long description"]
 *
 */

public class ExternalProcessor extends Processor.ProcessorSkeleton {
    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.ExternalProcessor");

    private final String call;
    private final String args;
    private final String shortName;
    private final String longName;
    private final Set<String> accepts;

    @ParamsViaArgumentObject
    public ExternalProcessor(Arguments arguments) {
        if (arguments.accepts == null || arguments.accepts == "") {
            this.accepts = null;
        } else {
            this.accepts =
                new LinkedHashSet<String>(Arrays.asList(arguments.accepts.split(" ")));;
        }
        this.args = arguments.args;
        this.call = arguments.call;
        this.longName = arguments.longName;
        this.shortName = arguments.shortName;
    }

    private String sname(){
        return this.shortName == null ? "External" : this.shortName;
    }

    private String name(){
        return this.longName == null ? this.sname()+"["+this.call+","+this.args+"]" : this.longName;
    }

    /**
     * this processor is applicable to all extern usable obligations (i.e. which
     * implement the interface ExternUsable)
     */
    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof ExternUsable) {
            if (this.accepts == null) {
                return true;
            }
            return this.accepts.contains(((ExternUsable)obl).externName());
        }
        return false;
    }

    private Result error(String msg){
        String out = this.name() + ": " + msg;
        ExternalProcessor.log.log(Level.FINEST, out+"\n");
        return ResultFactory.error(out);
    }

    private String scanToLine(BufferedReader reader, String endline) throws IOException{
        StringBuilder lines = new StringBuilder();
        String line = reader.readLine();
        while (!endline.equals(line)) {
            lines.append(line);
            lines.append("\n");
            line = reader.readLine();
        }
        return lines.toString();
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, final Abortion aborter, RuntimeInformation rti) throws AbortionException{
        Process process = null;
        try {
            ExternUsable eu = (ExternUsable)obl;
            ArrayList<String> parameters = new ArrayList<String>();
            parameters.add(this.call);
            parameters.add(eu.externName());
            parameters.addAll(Arrays.asList(this.args.split(" ")));
            ProcessBuilder processBuilder = new ProcessBuilder(parameters.toArray(new String[]{}));
            process = processBuilder.start();
            TrackerFactory.process(aborter, process);
//            Scanner sc = new Scanner(process.getErrorStream());
            BufferedReader stdOut = new BufferedReader(new InputStreamReader(process.getInputStream()));
            Writer inputWriter = new OutputStreamWriter(process.getOutputStream());
            inputWriter.write(eu.toExternString());
            inputWriter.close();

            ExternalProcessor.log.log(Level.FINEST, obl.getName(NameLength.LONG)+" transfered to external processor\n");
            ExternalProcessor.log.log(Level.INFO, "Starting external processor\n");
            ExternalProcessor.log.log(Level.FINEST, "  Calling: "+this.call+" "+eu.externName()+" "+this.args+"\n");

            return this.extractResult(oblNode, rti, stdOut);
        } catch (ParserErrorsSourceException e){
            return this.error(e.getMessage());
        } catch (SourceException e){
            return this.error(e.getMessage());
        } catch (NotExternUsableInstanceException e) {
            return this.error(e.getMessage());
        } catch (IOException e) {
            e.printStackTrace();
            return this.error("IO Error");
        } finally {
            if (process != null)
             {
                process.destroy(); // clean up
            }
        }
    }

    private Result extractResult(BasicObligationNode oblNode,
            RuntimeInformation rti, BufferedReader stdOut) throws IOException,
            ParserErrorsSourceException, SourceException {

        UserStrategy strategy = null;
        String line = stdOut.readLine();

        if (line == null) {
            return this.error("No output received");
        }

        if (line.startsWith("STRATEGY")) {
            String type = line.substring(8);
            String stratSpec = this.scanToLine(stdOut, "END STRATEGY");
            if (type.equals(" SIMPLE")) {
                ExternalProcessor.log.log(Level.FINEST, "Reading simple strategy\n");
                strategy = new VariableStrategy(stratSpec.trim());
            } else if (type.equals(" PROGRAM")) {
                ExternalProcessor.log.log(Level.FINEST, "Reading strategy program\n");
                StrategyProgram stratProg = EasyInput.parseStrategy(stratSpec);
                strategy = stratProg.lookup("main");
            } else {
                ExternalProcessor.log.log(Level.FINEST, "Strategy type unknown or missing");
                return this.error("Strategy specification invalid");
            }
            line = stdOut.readLine();
        }

        ExternalProcessor.log.log(Level.FINEST, "Receiving proof\n");
        if (line.startsWith("PROOF")){
            String direction = line.substring(5);
            Implication imp = null;
            if (direction.equals(" SOUND")){
                ExternalProcessor.log.log(Level.FINEST, "Methode is SOUND\n");
                imp = YNMImplication.SOUND;
            } else if (direction.equals(" COMPLETE")){
                ExternalProcessor.log.log(Level.FINEST, "Methode is COMPLETE\n");
                imp = YNMImplication.COMPLETE;
            } else if (direction.equals(" EQUIVALENT")){
                ExternalProcessor.log.log(Level.FINEST, "Methode is SOUND and COMPLETE\n");
                imp = YNMImplication.EQUIVALENT;
            } else {
                ExternalProcessor.log.log(Level.FINEST, "Implication missing\n");
                return this.error("Implication missing");
            }
            String proofStr = this.scanToLine(stdOut,"END PROOF");
            ExternalProcessor.log.log(Level.INFO, "Recieved proof\n");
            String next = stdOut.readLine();
            boolean or_and = false;
            if (next.equals("OR")) {
                or_and = false;
                ExternalProcessor.log.log(Level.FINEST, "Receiving OR-Obligation\n");
            } else if (next.equals("AND")) {
                ExternalProcessor.log.log(Level.FINEST, "Receiving AND-Obligation\n");
                or_and = true;
            } else {
                return this.error("Operator missing");
            }
            ExternalProcessor.log.log(Level.FINEST, "Receiving obligations\n");
            List<BasicObligationNode> positions = new ArrayList<BasicObligationNode>();
            List<ObligationNode> andOrNodes = new ArrayList<ObligationNode>();
            do {
                next = stdOut.readLine();
                if (next.startsWith("OBLIGATION ")){
                    String ext = next.substring(11);
                    String strObl = this.scanToLine(stdOut,"END OBLIGATION");
                    TypedInput typedInput = new ExtensionTypeAnalyzer().analyze(new StringInput(strObl, "externalInput", ext));
                    AnnotatedInput annoInput = new DefaultAnnotator().annotate(typedInput);
                    Pair<ObligationNode, List<BasicObligationNode>> rootAndPositions =
                            new MetaObligationFactory().getRootAndPositions(annoInput);
                    for(BasicObligationNode node: rootAndPositions.y) {
                        ExternalProcessor.log.log(Level.FINER, "Received "+node.getBasicObligation().getName(NameLength.LONG)+"\n");
                    }
                    andOrNodes.add(rootAndPositions.x);
                    positions.addAll(rootAndPositions.y);
                }
            } while (!next.equals("END"));
            ExternalProcessor.log.log(Level.INFO, "Received obligations\n");
            Proof proof = new ExternalProof(this.sname(), this.name(), proofStr);
            if (strategy == null || positions.size() == 0) {
                if (or_and) {
                    return ResultFactory.provedAndJunctorObligations(andOrNodes, positions, imp, proof);
                } else {
                    return ResultFactory.provedOrJunctorObligations(andOrNodes, positions, imp, proof);
                }
            } else {
                List<ExecutableStrategy> exStrs = new ArrayList<ExecutableStrategy>(positions.size());
                for(BasicObligationNode newNode: positions) {
                    exStrs.add(strategy.getExecutableStrategy(newNode, rti));
                }
                if (or_and) {
                    ExecutableStrategy exStr = new ExecAllSequential(exStrs, rti);
                    return ResultFactory.provedAndWithNewStrategy(andOrNodes, imp, proof, exStr);
                } else {
                    ExecutableStrategy exStr = new ExecAny(exStrs, rti);
                    return ResultFactory.provedOrWithNewStrategy(andOrNodes, imp, proof, exStr);
                }
            }
        } else if (line.equals("FAIL")) {
            ExternalProcessor.log.log(Level.FINEST, "Receiving failing reason\n");
            String reason = this.scanToLine(stdOut,"END");
            ExternalProcessor.log.log(Level.FINEST, "Received reason\n");
            if (strategy == null) {
                return ResultFactory.unsuccessful(reason);
            } else {
                ExecutableStrategy exStr = strategy.getExecutableStrategy(oblNode, rti);
                // TODO - Reason gets lost. Oh well...
                return ResultFactory.justANewStrategy(exStr);
            }
        } else {
            ExternalProcessor.log.log(Level.FINEST, "Received unkown result");
            return this.error("Output format incorrect");
        }
    }

    public String getAccepts() {
        StringBuilder exts = new StringBuilder();
        if (this.accepts != null){
            for (String ext : this.accepts){
                exts.append(ext);
                exts.append(" ");
            }
        }
        return exts.toString();
    }

    public String getLongName() {
        return this.longName;
    }

    public String getShortName() {
        return this.shortName;
    }

    public String getArgs() {
        return this.args;
    }

    public String getCall() {
        return this.call;
    }

    private static class ExternalProof extends Proof.DefaultProof {

        private String proofStr;

        public ExternalProof(String sname, String lname, String proofStr) {
            this.setShortName(sname);
            this.setLongName(lname);
            this.proofStr = proofStr;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            for (String s : this.proofStr.split("\n")){
                result.append(s);
                result.append(o.newline());
            }
            return result.toString();
        }


    }

    public static class Arguments {
        public String accepts;
        public String args;
        public String call;
        public String longName;
        public String shortName;
    }
}
