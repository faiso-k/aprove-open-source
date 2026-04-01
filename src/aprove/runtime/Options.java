package aprove.runtime;

import static aprove.verification.dpframework.JBCProblem.BareJBCProblem.*;
import static aprove.verification.oldframework.Bytecode.JBCOptions.*;
import static aprove.verification.oldframework.Bytecode.Processors.BareJBCToJBCProcessor.BareJBCOptions.*;

import java.io.*;
import java.util.*;

import aprove.cli.*;
import aprove.exit.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.Options.JBCAnalysisOptions.*;
import aprove.verification.oldframework.Bytecode.Processors.*;
import aprove.verification.oldframework.Bytecode.Processors.ToComplexity.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.WeightedIntTrs.*;

/**
 * This class serves as an analogon to aprove.Globals.
 * The core difference is that while Globals contains compile-time constants,
 * this file contains flags that affect the whole AProVE instance,
 * but are only known at runtime.
 *
 * Most of these flags were pulled from aprove.CommandLineOptions.Main to allow
 * other startup methods to cleanly set those flags as well.
 */
public class Options {

    public static class JBCAnalysisOptions {

        public static boolean Competition = false;

        public static enum AvailableOptions {
            path_to_method_summaries("path to a json file containing method summaries", Optional.of(String.class), false),
            path_to_library("path to a jar file containing library classes that should be avilable for the analysis", Optional.of(String.class), true),
            library_dir("path to a directory containing jar files with classes that should be avilable for the analysis", Optional.of(String.class), true),
            summarize_all_library_calls("summarize all calls to library methods using default summaries", Optional.of(Boolean.class), false),
            summarize_all_method_calls("summarize all method calls using default summaries", Optional.of(Boolean.class), false),
            summarize_recursive_methods("summarize all methods which turn out to be recursive during the analysis using default summaries", Optional.of(Boolean.class), false),
            analysis_goal("time_complexity, space_complexity, or termination (which is the default)", Optional.of(String.class), true),
            summarize_library_calls_with_more_states("summarize library methods whose evaluation on average results in at least that many states using default summaries", Optional.of(Integer.class), false),
            summarize_unimplemented_native_methods("summarize unimplemented native methods using default summaries", Optional.of(Boolean.class), false),
            avoid_expanding_type_tree("try not to expand the whole type tree, i.e., don't refine jlO, but do whatever the (sound) alternative is", Optional.of(Boolean.class), true),
            dont_expand_type_tree("don't expand the whole type tree, i.e., don't refine jlO, but do whatever the alternative is (e.g., use default summaries)", Optional.of(Boolean.class), false),
            warn_when_creating_default_summaries("print a warning whenever a default summary is created", Optional.of(Boolean.class), true),
            continue_on_missing_implementations("don't fail if a method is invoked, but there's no suitable implementation in the class path", Optional.of(Boolean.class), false),
            summarize_on_missing_implementations("use a default summary if a method is invoked, but there's no suitable implementation in the class path", Optional.of(Boolean.class), false),
            dump_default_summaries("dump all default summaries that were created during the analysis to a file", Optional.of(Boolean.class), true),
            path_to_graph_dump_directory("dumps the termination graph to a dot file to the given directory", Optional.of(String.class), true),
            dump_intermediate_termination_graphs("dump intermediate termination graphs to dot files", Optional.of(Boolean.class), true),
            incorrectly_bound_size_of_constant_strings_by_length("add the constraint s <= s.length to ths ITS if s is a string constant; note that this does not correspond to our usual measure of size", Optional.of(Boolean.class), false),
            boot_jvm("symbolically evaluate the startup of the jvm; since this is not needed at TermComp, we consider this option to be sound", Optional.of(String.class), true),
            default_class_init_state("sets the default class initialization state", Optional.of(YNM.class), true),
            competition("set all options as required for the competition", Optional.empty(), true),
            cage("set all options as required for CAGE toolchain", Optional.empty(), false),
            simplified_string_handling("don't care about complicated stuff like the constant pool for strings; since this is not needed at TermComp, we consider this option to be sound", Optional.of(Boolean.class), true),
            simplified_class_handling("don't care about complicated stuff like the constant pool for class-objects; since this is not needed at TermComp, we consider this option to be sound", Optional.of(Boolean.class), true),
            load_all_native_methods("load all implemented native methods and not just those required for TermComp", Optional.of(Boolean.class), true),
            show_lower_bounds("show lower bound proven for the resulting ITS, even though the transformation is unsound", Optional.of(Boolean.class), false),
            input_array_exists("can we assume that the input array of main exists?", Optional.of(Boolean.class), true),
            indicate_progress("print a dot every 100 states to indicate that AProVE is still doing something", Optional.of(Boolean.class), true),
            dump_method_info_to("dumps information about the analyzed method (number of loops, number of branches...) to the given file", Optional.of(String.class), true),
            help("print a help message explaining the available options for the analysis of java bytecode", Optional.empty(), true);



            String description;
            Optional<Class<?>> argType;
            boolean sound;

            AvailableOptions(String description, Optional<Class<?>> argType, boolean sound) {
                this.description = description;
                this.argType = argType;
                this.sound = sound;
            }

            void printHelp() {
                System.out.println();
                System.out.println("name: " + this);
                if (argType.isPresent()) {
                    String name = argType.get().getName();
                    int index = name.lastIndexOf(".");
                    if (index > 0) {
                        name = name.substring(index + 1);
                    }
                    System.out.println("expected argument: " + name);
                } else {
                    System.out.println("no argument expected");
                }
                System.out.println("description: " + description);
                if (!sound) {
                    System.out.println("Enabling this feature makes AProVE UNSOUND!");
                }
                System.out.println();
            }

        }

        static StaticOption<?>[] staticOptions =
            {
             cliPathToMethodSummaries,
             cliLibraryJars,
             cliSummarizeAllLibraryCalls,
             cliSummarizeAllMethodCalls,
             cliSummarizeRecursiveMethods,
             cliGoal,
             cliSummarizeLibraryCallsWithMoreStates,
             cliSummarizeUnimplementedNativeMethods,
             cliAvoidExpandingTypeTree,
             cliDontExpandTypeTree,
             cliContinueOnMissingImplementations,
             cliSummarizeOnMissingImplementations,
             cliDumpDefaultSummaries,
             cliPathToGraphDumpDirectory,
             cliDumpIntermediateTerminationGraphs,
             cliIncorrectlyBoundSizeOfConstantStringsByLength,
             cliBootJVM,
             cliDefaultClassInitState,
             cliSimplifiedStringHandling,
             cliSimplifiedClassHandling,
             cliLoadAllNativeMethods,
             WeightedIntTrsRemoveUnsupportedOperatorsProcessor.Arguments.cliPropagateLowerBounds,
             JBCGraphEdgesToIntTrsProcessor.Arguments.cliPropagateLowerBounds,
             WeightedIntTrsStraightLineCodeCompressionProcessor.Arguments.cliPropagateLowerBounds,
             SEGraphFlowAnalysisProcessor.Arguments.cliPropagateLowerBounds,
             WeightedIntTrsUnneededArgumentFilterProcessor.Arguments.cliPropagateLowerBounds,
             WeightedIntTrsDuplicateArgumentFilterProcessor.Arguments.cliPropagateLowerBounds,
             cliInputArrayExists,
             cliIndicateProgress,
             cliDumpMethodInfoTo
            };

        public void restoreDefaults() {
            for (StaticOption<?> so: staticOptions) {
                so.reset();
            }
        }

        public JBCAnalysisOptions() {
            if (Competition) {
                setSafe(AvailableOptions.competition, Optional.of("true"));
            }
        }

        public void set(AvailableOptions option, Optional<String> valueArg) throws KillAproveException {
            Optional<String> value = valueArg.map(x -> x.trim());
            try {
                switch (option) {
                    case library_dir: {
                        assert value.isPresent();
                        File dir = new File(value.get());
                        if (!dir.exists()) {
                            System.err.println("Path " + value.get() + " does not exist.");
                            throw new KillAproveException(-1);
                        }
                        if (!dir.isDirectory()) {
                            System.err.println(value.get() + " is not a path.");
                            throw new KillAproveException(-1);
                        }
                        for (String jar: dir.list((directory, filename) -> filename.endsWith("jar"))) {
                            addCliLibraryJar(new File(dir.getAbsolutePath() + File.separator + jar));
                        }
                        break;
                    }
                    default: {
                        setSafe(option, valueArg);
                        break;
                    }
                }
            } catch (IllegalArgumentException e) {
                throw new RuntimeException("unknown java-option " + option);
            }
        }

        public void setSafe(AvailableOptions option, Optional<String> valueArg) {
            Optional<String> value = valueArg.map(x -> x.trim());
            try {
                switch (option) {
                    case path_to_method_summaries: {
                        assert value.isPresent();
                        cliPathToMethodSummaries.set(value);
                        break;
                    }
                    case path_to_library: {
                        assert value.isPresent();
                        addCliLibraryJar(new File(value.get()));
                        break;
                    }
                    case summarize_all_library_calls: {
                        assert value.isPresent();
                        cliSummarizeAllLibraryCalls.set(Boolean.parseBoolean(value.get()));
                        break;
                    }
                    case summarize_all_method_calls: {
                        assert value.isPresent();
                        cliSummarizeAllMethodCalls.set(Boolean.parseBoolean(value.get()));
                        break;
                    }
                    case summarize_recursive_methods: {
                        assert value.isPresent();
                        cliSummarizeRecursiveMethods.set(Boolean.parseBoolean(value.get()));
                        break;
                    }
                    case summarize_library_calls_with_more_states: {
                        assert value.isPresent();
                        cliSummarizeLibraryCallsWithMoreStates.set(Integer.parseInt(value.get()));
                        break;
                    }
                    case analysis_goal: {
                        assert value.isPresent();
                        String val = value.get();
                        // required to keep the API stable for our CAGE project
                        switch (val) {
                            case "space_complexity":
                                val = "SpaceComplexity";
                                break;
                            case "time_complexity":
                                val = "RuntimeComplexity";
                                break;
                            case "termination":
                                val = "Termination";
                                break;
                            default:
                                try {
                                    HandlingMode.valueOf(val);
                                } catch (IllegalArgumentException e) {
                                    throw new RuntimeException("don't know how to analyze " + value.get());
                                }
                                break;
                        }
                        String finalVal = val;
                        Optional<HandlingMode> mode = HandlingMode.valueOfIgnoreCase(finalVal);
                        cliGoal.set(mode.orElseThrow(() -> new RuntimeException("don't know how to analyse " + finalVal)));
                        break;
                    }
                    case summarize_unimplemented_native_methods: {
                        assert value.isPresent();
                        cliSummarizeUnimplementedNativeMethods.set(Boolean.parseBoolean(value.get()));
                        break;
                    }
                    case dont_expand_type_tree: {
                        assert value.isPresent();
                        boolean val = Boolean.parseBoolean(value.get());
                        cliDontExpandTypeTree.set(val);
                        if (val) {
                            cliAvoidExpandingTypeTree.set(true);
                        }
                        break;
                    }
                    case warn_when_creating_default_summaries: {
                        System.err.println("warn_when_creating_default_summaries is no longer supported -- please set a logging level >= INFO for aprove.verification.oldframework.Bytecode instead");
                        break;
                    }
                    case continue_on_missing_implementations: {
                        assert value.isPresent();
                        cliContinueOnMissingImplementations.set(Boolean.parseBoolean(value.get()));
                        break;
                    }
                    case summarize_on_missing_implementations: {
                        assert value.isPresent();
                        cliSummarizeOnMissingImplementations.set(Boolean.parseBoolean(value.get()));
                        break;
                    }
                    case dump_default_summaries: {
                        assert value.isPresent();
                        cliDumpDefaultSummaries.set(Boolean.parseBoolean(value.get()));
                        break;
                    }
                    case path_to_graph_dump_directory: {
                        assert value.isPresent();
                        cliPathToGraphDumpDirectory.set(value);
                        break;
                    }
                    case dump_intermediate_termination_graphs: {
                        assert value.isPresent();
                        cliDumpIntermediateTerminationGraphs.set(Boolean.parseBoolean(value.get()));
                        break;
                    }
                    case incorrectly_bound_size_of_constant_strings_by_length: {
                        assert value.isPresent();
                        cliIncorrectlyBoundSizeOfConstantStringsByLength.set(Boolean.parseBoolean(value.get()));
                        break;
                    }
                    case indicate_progress: {
                        assert value.isPresent();
                        cliIndicateProgress.set(Boolean.parseBoolean(value.get()));
                        break;
                    }
                    case avoid_expanding_type_tree: {
                        assert value.isPresent();
                        boolean val = Boolean.parseBoolean(value.get());
                        cliAvoidExpandingTypeTree.set(val);
                        if (!val)  {
                            cliDontExpandTypeTree.set(false);
                        }
                        break;
                    }
                    case boot_jvm: {
                        assert value.isPresent();
                        cliBootJVM.set(JVMBoot.valueOf(value.get()));
                        break;
                    }
                    case default_class_init_state: {
                        assert value.isPresent();
                        cliDefaultClassInitState.set(InitStatus.valueOf(value.get()));
                        break;
                    }
                    case competition: {
                        assert !value.isPresent();
                        cliBootJVM.set(JVMBoot.Competition);
                        cliDefaultClassInitState.set(InitStatus.NO);
                        cliSimplifiedStringHandling.set(true);
                        cliSimplifiedClassHandling.set(true);
                        cliLoadAllNativeMethods.set(false);
                        cliInputArrayExists.set(true);
                        Competition = true;
                        break;
                    }
                    case cage: {
                        assert !value.isPresent();
                        cliBootJVM.set(JVMBoot.None);
                        cliDefaultClassInitState.set(InitStatus.YES);
                        cliSimplifiedStringHandling.set(true);
                        cliSimplifiedClassHandling.set(true);
                        cliLoadAllNativeMethods.set(true);
                        cliInputArrayExists.set(true);
                        cliSummarizeAllMethodCalls.set(true);
                        cliDontExpandTypeTree.set(true);
                        cliIncorrectlyBoundSizeOfConstantStringsByLength.set(true);
                        Competition = false;
                        break;
                    }
                    case simplified_string_handling: {
                        assert value.isPresent();
                        cliSimplifiedStringHandling.set(Boolean.valueOf(value.get()));
                        break;
                    }
                    case simplified_class_handling: {
                        assert value.isPresent();
                        cliSimplifiedClassHandling.set(Boolean.valueOf(value.get()));
                        break;
                    }
                    case load_all_native_methods: {
                        assert value.isPresent();
                        cliLoadAllNativeMethods.set(Boolean.valueOf(value.get()));
                        break;
                    }
                    case input_array_exists: {
                        assert value.isPresent();
                        cliInputArrayExists.set(Boolean.valueOf(value.get()));
                        break;
                    }
                    case show_lower_bounds: {
                        assert value.isPresent();
                        boolean val = Boolean.valueOf(value.get());
                        WeightedIntTrsRemoveUnsupportedOperatorsProcessor.Arguments.cliPropagateLowerBounds.set(val);
                        JBCGraphEdgesToIntTrsProcessor.Arguments.cliPropagateLowerBounds.set(val);
                        WeightedIntTrsStraightLineCodeCompressionProcessor.Arguments.cliPropagateLowerBounds.set(val);
                        SEGraphFlowAnalysisProcessor.Arguments.cliPropagateLowerBounds.set(val);
                        WeightedIntTrsUnneededArgumentFilterProcessor.Arguments.cliPropagateLowerBounds.set(val);
                        WeightedIntTrsDuplicateArgumentFilterProcessor.Arguments.cliPropagateLowerBounds.set(val);
                        break;
                    }
                    case dump_method_info_to: {
                        assert value.isPresent();
                        cliDumpMethodInfoTo.set(value);
                        break;
                    }
                    case help: {
                        assert !value.isPresent();
                        printHelp();
                        System.exit(0);
                        break;
                    }
                    default: {
                        printHelp();
                        throw new RuntimeException("The java-option " + option + " should exist, but is not yet implemented...");
                    }
                }
            } catch (IllegalArgumentException e) {
                throw new RuntimeException("unknown java-option " + option);
            }
        }

        private void printHelp() {
            System.out.println("Available java-options are:");
            for (AvailableOptions o: AvailableOptions.values()) {
                o.printHelp();
            }
        }

    }

    public static JBCAnalysisOptions jbcOptions = new JBCAnalysisOptions();

    /** If the proof is to be embedded in another HTML Page (Hint: competition) */
    public static boolean embedHtmlProof = false;

    /**
     * The path to a lemma database to import, for theorem prover
     */
    public static String lemmaDatabaseFileName = null;

    /**
     * returns a filename where haskell modules are stored (option -h)
     */
    public static String serializationModulesSource = null;

    /**
     * If this and exampleId are set, each finished processor will be logged
     * to a csv format for performance measurement
     */
    public static String csvName = null;
    public static Integer exampleId = null;

    /**
     * If true, some processor proofs will render a PNG graph and link it
     * in the proof
     * @deprecated we do not have JDotty anymore
     */
    @Deprecated
    public static boolean exportGraphs = false;

    /**
     * true if we were started from a CGI script.
     *
     * This makes some Haskell pieces spontaneously emit HTML to stdout on error,
     * as well as disabling some features that might be dangerous from untrusted users.
     */
    public static boolean isWebInterfaceMode = false;

    /**
     * Should e.g. strategy programs be checked for errors early, as opposed to lazily?
     */
    public static boolean performEagerChecking = true;

    /**
     * Certifier used, necessary to restrict our techniques to only what
     * certifier supports.
     */
    public static Certifier certifier = Certifier.NONE;

    /**
     * Here we can decide whether we want certification of each proof step,
     * the String is the directory where the partial certificates should be stored
     */
    public static String onlineCertification = null;

    /**
     * If false, new threads (i.e. processor executions) are queued if we are running
     * more than our thread pool likes to. If true, they are started immediately anyway.
     */
    public static boolean defaultThreadingHasPriority = true;

    /**
     * If true, strategy primitives that have uncertain results
     * (i.e. First, Any) are encouraged to copy the input ObligationNode
     * and attempt solving on a copy, only merging the copy into the proof tree
     * when success is certain.
     *
     * This helps keep a neat proof tree, but the merge process is said to
     * be overly expensive if many nodes are generated (i.e. theorem prover)
     */
    public static boolean strategyWorksOnCopies = false; // Used to default to true in release mode

    /**
     * this method was supposed to allow enabling graph exports for specific
     * Export_Util instances. The corresponding setter was never used.
     *
     * If it is needed at some point, recommend using a ThreadLocal instead,
     * which should work much better than relying on a specific Export_Util instance.
     * @param that unused now. This method always returns false.
     * @deprecated reimplement with ThreadLocal if needed.
     */
    @Deprecated
    public static boolean exportGraphsForThatInstance(final Export_Util that) {
        return false;
    }

    /**
     * Sets an option by name.
     * @throws KillAproveException
     */
    public static void set(String optionArg, final Optional<String> value) throws KillAproveException {
        String option = optionArg.toLowerCase().trim();

        if (option.startsWith("java::")) {
            String rawJbcOption = option.substring("java::".length());
            String jbcOption = rawJbcOption.trim();
            jbcOptions.set(AvailableOptions.valueOf(jbcOption), value);
        } else if (option.equals("eagercheck")) {
            performEagerChecking = Boolean.parseBoolean(value.get());
        } else {
            System.err.println("Unrecognized option '" + option + "' requested, ignoring.");
        }
    }
}
