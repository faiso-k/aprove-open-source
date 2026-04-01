package aprove;

public abstract class Globals {
    // current developers
    static final long NONE = 0L;
    static final long SWISTE = 1 << 0;
    static final long NOWONDER = 1L << 1;
    static final long RABE = 1L << 2;
    static final long THIEMANN = 1L << 3;
    static final long FUHS = 1L << 4;
    static final long MATRAF = 1L << 5;
    static final long SPECIALMAN = 1L << 6;
    static final long PATWIE = 1L << 7;
    static final long DICKMEIS = 1L << 8;
    static final long STEIN = 1L << 9;
    static final long MARMER = 1L << 10;
    static final long CRYINGSHADOW = 1L << 11;
    static final long COTTO = 1L << 12;
    static final long KABASCI = 1L << 13;
    static final long PROMETHEUS = 1L << 14;
    static final long WEIDMANN = 1L << 15;
    static final long BEARPERSON = 1L << 16;
    static final long PAUL = 1L << 17;
    static final long FAB = 1L << 18;
    static final long NOSCHINSKI = 1L << 19;
    static final long SPF = 1L << 20;
    static final long ULRICHSG = 1L << 21;
    static final long THETUX = 1L << 22;
    static final long MPLUECKER = 1L << 23;
    static final long MICPAR = 1L << 24;
    static final long MARC = 1L << 25;
    static final long CHRISTIAN = 1L << 26;
    static final long CKUKNAT = 1L << 27;
    static final long SEBWEI = 1L << 28;
    static final long NEX = 1L << 29;
    static final long FKUERTEN = 1L << 30;
    static final long MATTHIAS = 1L << 31;
    static final long JANINE = 1L << 32;
    static final long MARCEL = 1L << 33;
    static final long ALBHEL = 1L << 34;
    static final long RICHARD = 1L << 35;
    static final long FFROHN = 1L << 36;
    static final long SKIELMANN = 1L << 37;
    static final long THIES = 1L << 38;
    static final long FBIER = 1L << 39;
    static final long FEMRICH = 1L << 40;
    static final long MARINAG = 1L << 41;
    static final long MNAAF = 1L << 42;
    static final long KASSING = 1L << 43;

    /*
     * Set these values in GlobalSettings.java (create this file based on
     * GlobalSettingsTemplate.java).
     */
    // set to the sum of the developers whose debug messages you want
    // to see in your working copy; leave at NONE in the repository version
    private static final long DEBUG_MODE = GlobalSettings.DEBUG_MODE;
    public static final AproveVersion aproveVersion =
        GlobalSettings.aproveVersion;
    
    public static String bitwidth;
    
    public static boolean generateGraphmlWitness = false;
    
    public static String programFile;
    
    public static int INSTRUCTION_COUNT_THRESHOLD = 480;

    /** For QCSDPs. Use simple Ren^mu(Cap^mu(...)) instead of ICap^mu */
    /*
     * TODO To avoid this global flag one would have to modify the QCSDPProblem and
     * QCSDependencyGraph. The graph must not be approximated in the problem, but only
     * when applying the QCSDependencyGraph processor. This change would allow to
     * parameterize the dependency graph processor. This also implies that one would
     * have to recheck every edge when applying the QCSDependencyGraph, since one would
     * not know whether the edge was checked with the same estimations before.
     *
     * Note that the same problem also exists for the QDependencyGraph and possibly for
     * other processors, too.
     */
    public static final boolean simpleCapMu = GlobalSettings.simpleCapMu;

    /**
     * If true, attempt to start external processes using an external "spawner"
     * daemon rather than directly via the VM. This can speed up these launches,
     * especially if the VM is using a lot of memory.
     * Currently only the regular MinisatEngine uses this mechanism.
     * However, this requires bin/minisatd.c to be compiled and placed into PATH
     * as "minisatd".
     */
    public static final boolean useExternalSpawner = GlobalSettings.useExternalSpawner;

    // Create labels for propositional formulae? (For use in SATView or even plain debugging).
    // Labels will be quietly ignored if false - saves memory for release version.
    // As the final formulae will have a slightly different structure, do a regression test!
    public static final boolean createSatViewLabels = GlobalSettings.createSatViewLabels;

    /**
     * If set, for every processor some "profiling" output in form of <br>
     * "prefix processorName startTime cpuTime wallTime startegyResult parameters"<br>
     * for "processor profiling" prefix is PROFILE_PREFIX_PROCESSOR<br>
     * and for "strategy profiling" prefix is PROFILE_PREFIX_STRATEGY<br>
     * with timeformat of msec is printed on stderr
     */
    public static final boolean PROFILING = GlobalSettings.PROFILING;
    public final static String PROFILE_PREFIX_PROCESSOR = "profile_proc:";
    public final static String PROFILE_PREFIX_STRATEGY = "profile_strat:";
    public final static String PROFILE_PREFIX_FEATURE = "profile_feat:";
    public static final long startUpTime = System.currentTimeMillis();

    /*
     * This toggles the collection of training data for machine learning mechanisms. Currently SVM only.
     */
    public static final boolean TRAINING = GlobalSettings.TRAINING;

    /*
     * If set, produce nodes in the proof tree for every processor.
     *
     * I.e. even processors, which did not deliver a result (because they failed
     * or were aborted) show up in the proof tree. May be useful for strategy
     * analysis.
     */
    public static final boolean FULL_PROOF_TREE =
        GlobalSettings.FULL_PROOF_TREE;

    /**
     * This toggles if the needed time is exported in the proof.
     */
    public static final boolean TIMINGS_IN_PROOF_TREE =
        GlobalSettings.TIMINGS_IN_PROOF_TREE;

    /**
     * If this is set, the benchmark framework will log all uncaught exceptions
     * to the database (which must be able to store them, see a recent database
     * template).
     */
    public static final boolean logExceptionsInBenchmarkMode =
        GlobalSettings.logExceptionsInBenchmarkMode;
    public static final boolean useAssertions = areAssertionsActivated();

    public static final boolean DEBUG_NONE = Globals.DEBUG_MODE == Globals.NONE;
    public static final boolean DEBUG_SWISTE = (Globals.DEBUG_MODE & Globals.SWISTE) != 0;
    public static final boolean DEBUG_SWISTE2 = (Globals.DEBUG_MODE & Globals.SWISTE) != 0;
    public static final boolean DEBUG_NOWONDER = (Globals.DEBUG_MODE & Globals.NOWONDER) != 0;
    public static final boolean DEBUG_RABE = (Globals.DEBUG_MODE & Globals.RABE) != 0;
    public static final boolean DEBUG_THIEMANN = (Globals.DEBUG_MODE & Globals.THIEMANN) != 0;
    public static final boolean DEBUG_FUHS = (Globals.DEBUG_MODE & Globals.FUHS) != 0;
    public static final boolean DEBUG_MATRAF = (Globals.DEBUG_MODE & Globals.MATRAF) != 0;
    public static final boolean DEBUG_SPECIALMAN =
        (Globals.DEBUG_MODE & Globals.SPECIALMAN) != 0;
    public static final boolean DEBUG_PATWIE = (Globals.DEBUG_MODE & Globals.PATWIE) != 0;
    public static final boolean DEBUG_DICKMEIS = (Globals.DEBUG_MODE & Globals.DICKMEIS) != 0;
    public static final boolean DEBUG_STEIN = (Globals.DEBUG_MODE & Globals.STEIN) != 0;
    public static final boolean DEBUG_MARMER = (Globals.DEBUG_MODE & Globals.MARMER) != 0;
    public static final boolean DEBUG_CRYINGSHADOW =
        (Globals.DEBUG_MODE & Globals.CRYINGSHADOW) != 0;
    public static final boolean DEBUG_COTTO = (Globals.DEBUG_MODE & Globals.COTTO) != 0;
    public static final boolean DEBUG_KABASCI = (Globals.DEBUG_MODE & Globals.KABASCI) != 0;
    public static final boolean DEBUG_PROMETHEUS =
        (Globals.DEBUG_MODE & Globals.PROMETHEUS) != 0;
    public static final boolean DEBUG_WEIDMANN = (Globals.DEBUG_MODE & Globals.WEIDMANN) != 0;
    public static final boolean DEBUG_BEARPERSON =
        (Globals.DEBUG_MODE & Globals.BEARPERSON) != 0;
    public static final boolean DEBUG_PAUL = (Globals.DEBUG_MODE & Globals.PAUL) != 0;
    public static final boolean DEBUG_FAB = (Globals.DEBUG_MODE & Globals.FAB) != 0;
    public static final boolean DEBUG_NOSCHINSKI =
        (Globals.DEBUG_MODE & Globals.NOSCHINSKI) != 0;
    public static final boolean DEBUG_SPF = (Globals.DEBUG_MODE & Globals.SPF) != 0;
    public static final boolean DEBUG_ULRICHSG = (Globals.DEBUG_MODE & Globals.ULRICHSG) != 0;
    public static final boolean DEBUG_THETUX = (Globals.DEBUG_MODE & Globals.THETUX) != 0;
    public static final boolean DEBUG_MPLUECKER = (Globals.DEBUG_MODE & Globals.MPLUECKER) != 0;
    public static final boolean DEBUG_MICPAR = (Globals.DEBUG_MODE & Globals.MICPAR) != 0;
    public static final boolean DEBUG_MARC = (Globals.DEBUG_MODE & Globals.MARC) != 0;
    public static final boolean DEBUG_CHRISTIAN = (Globals.DEBUG_MODE & Globals.CHRISTIAN) != 0;
    public static final boolean DEBUG_CKUKNAT = (Globals.DEBUG_MODE & Globals.CKUKNAT) != 0;
    public static final boolean DEBUG_SEBWEI = (Globals.DEBUG_MODE & Globals.SEBWEI) != 0;
    public static final boolean DEBUG_NEX = (Globals.DEBUG_MODE & Globals.NEX) != 0;
    public static final boolean DEBUG_FKUERTEN = (Globals.DEBUG_MODE & Globals.FKUERTEN) != 0;
    public static final boolean DEBUG_MATTHIAS = (Globals.DEBUG_MODE & Globals.MATTHIAS) != 0;
    public static final boolean DEBUG_JANINE = (Globals.DEBUG_MODE & Globals.JANINE) != 0;
    public static final boolean DEBUG_MARCEL = (Globals.DEBUG_MODE & Globals.MARCEL) != 0;
    public static final boolean DEBUG_ALBHEL = (Globals.DEBUG_MODE & Globals.ALBHEL) != 0;
    public static final boolean DEBUG_RICHARD = (Globals.DEBUG_MODE & Globals.RICHARD) != 0;
    public static final boolean DEBUG_FFROHN = (Globals.DEBUG_MODE & Globals.FFROHN) != 0;
    public static final boolean DEBUG_SKIELMANN = (Globals.DEBUG_MODE & Globals.SKIELMANN) != 0;
    public static final boolean DEBUG_THIES = (Globals.DEBUG_MODE & Globals.THIES) != 0;
    public static final boolean DEBUG_FBIER = (Globals.DEBUG_MODE & Globals.FBIER) != 0;
    public static final boolean DEBUG_FEMRICH = (Globals.DEBUG_MODE & Globals.FEMRICH) != 0;
    public static final boolean DEBUG_MARINAG = (Globals.DEBUG_MODE & Globals.MARINAG) != 0;
    public static final boolean DEBUG_MNAAF = (Globals.DEBUG_MODE & Globals.MNAAF) != 0;
    public static final boolean DEBUG_KASSING = (Globals.DEBUG_MODE & Globals.KASSING) != 0;

    private static boolean areAssertionsActivated() {
        boolean assertions = false;
        // Ridiculous, but silences compiler warnings. Effectively sets assertions=true iff assert() is enabled
        assert ((assertions = true) == true);
        return assertions;
    }

    static {
        if (Globals.PROFILING) {
            System.err.println("Processor Profiling enabled using the following format");
            System.err.println("\t << "+Globals.PROFILE_PREFIX_PROCESSOR+"\t obligationID processorName startTime cpuTime wallTime strategyResult parameters >>");
            System.err.println("\t << "+Globals.PROFILE_PREFIX_STRATEGY+"\t obligationID strategyName startTime cpuTime wallTime strategyResult parameters >>");
        }
    }

    public enum AproveVersion {
        RELEASE_VERSION("Head Release Version"), DEVELOPER_VERSION(
            "Head Developer Version");

        private final String showName;

        private AproveVersion(final String name) {
            this.showName = name;
        }

        @Override
        public String toString() {
            return this.showName;
        }
    }

    // to ensure that Globals is initialized
    public static void init(){

    }
}
