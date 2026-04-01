package aprove.strategies.ExecutableStrategies;

import java.io.*;
import java.util.concurrent.atomic.*;
import java.util.logging.*;

import aprove.*;
import aprove.logging.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Util.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.Profiling.*;

/**
 * Executors start Processors in a new Thread.
 * After the execution the result can be obtained by getResult.
 *
 * If run with low priority it may result in a not started state.
 * @author thiemann
 *
 */
public class Executor {

    /**
     * the log for logging everything
     */
    private static final Logger LOG = Logger.getAnonymousLogger();

    /**
     * the number which has to be executed next
     */
    private static final AtomicInteger NEXT_EXECUTOR_NR = new AtomicInteger(1);

    /**
     * runtime information
     */
    private final RuntimeInformation rti;

    /**
     * the obligation we are at
     */
    private final BasicObligationNode pos;

    /**
     * the processor itself
     */
    private final Processor proc;

    /**
     * short name for the processor
     */
    private final String shortName;

    /**
     * addendum of the proc (to be deleted, I hope)
     */
    private final String nameAddendum;

    /**
     * the time at which it is startet
     */
    private final long startUpTime;

    /**
     * a clock to measure wall and cpu time
     */
    private final Clock clock;

    /**
     * the abortion
     */
    private Abortion abortion;

    /**
     * the number of the executor
     */
    private int executorNr;

    /**
     * a result for this obligation
     */
    private volatile Result result;

    /**
     * create
     *
     * @param posArg of obligation
     * @param procArg that is executed
     * @param rtiArg information that is needed while runtime
     * @param shortNameArg of the proc
     * @param nameAddendumArg of the proc (to be deleted, maybe)
     */
    Executor(final BasicObligationNode posArg, final Processor procArg, final RuntimeInformation rtiArg,
            final String shortNameArg, final String nameAddendumArg) {
        this.rti = rtiArg;
        this.pos = posArg;
        this.proc = procArg;
        this.shortName = shortNameArg;
        this.nameAddendum = nameAddendumArg;
        this.startUpTime = System.currentTimeMillis();
        this.clock = new Clock();
    }

    /**
     * Start the execution
     */
    public void start() {
        final RuntimeInformation rtiForAbortion = this.rti.copyAddClock(this.clock);
        this.abortion = AbortionFactory.create(rtiForAbortion);
        this.executorNr = Executor.NEXT_EXECUTOR_NR.getAndIncrement();
        final Runner runner = new Runner(this.abortion);
        runner.setExceptionLogger((ExceptionLogger) this.rti.getMetadata(Metadata.EXCEPTION_LOGGER));
        this.rti.getThreadingPolicy().schedule(runner);
    }

    /**
     * getter for the result
     *
     * @return the result of the executor
     */
    Result getResult() {
        return this.result;
    }

    /**
     * setter for the result
     *
     * @param resultArg to be set
     */
    protected void setResult(final Result resultArg) {
        if (resultArg == null) {
            throw new NullPointerException("result");
        }
        synchronized (this) {
            if (this.result != null) {
                return;
            }
            this.result = resultArg;
        }

        this.logResult(resultArg);

        this.abortion.abort("Executor received result");
        this.rti.execute();
    }

    /**
     * method to log the result to the logger
     *
     * @param resultArg to be logged
     */
    protected void logResult(final Result resultArg) {
        // we have to log the resulting strategy as string,
        // as otherwise we may get concurrent modification exceptions.
        final long consumedTime = this.getFinalTime();

        if (resultArg.getObligationChild() != null) {
            resultArg.getObligationChild().setConsumedTime(consumedTime);
        }

        final String time = " within " + consumedTime + "ms";
        if (aprove.runtime.Options.exampleId != null && aprove.runtime.Options.csvName != null) {
            try {
                final FileWriter fw = new FileWriter(aprove.runtime.Options.csvName, true);
                fw.write(String.format("%d\t%s\t%s\t%d\t%s\n", aprove.runtime.Options.exampleId, this.proc.getClass().getCanonicalName(), this.nameAddendum, consumedTime, resultArg.getStrategy()));
                fw.close();
            } catch (final IOException e) {
                e.printStackTrace();
            }
        }

        if (Executor.LOG.isLoggable(Level.INFO)) {
            Executor.LOG.log(Level.INFO, (this.executorNr == 0 ? "" : System.nanoTime() / 1000000000 + " Exec."
                + this.executorNr + ", ")
                + "Processor {0} is done" + time + " with result " + resultArg.getStrategy() + ".\n", this.shortName);
        }

        if (Globals.PROFILING) {
            Writer wr;
            try {
                wr = Profiling.getWriter();
                synchronized (wr) {
                    // log processor
                    Executor.logProfile(Globals.PROFILE_PREFIX_PROCESSOR, this.pos,
                        this.shortName, this.nameAddendum, this.startUpTime,
                        this.getFinalTime(), resultArg.getStrategy(), wr);
                    final BasicObligation bObl = this.pos.getBasicObligation();
                    // cut obl-xxxx to xxxx
                    final int oblId = Integer.parseInt(bObl.getId().substring(4));
                    // write FeatureVector
                    if (!Profiling.getObligationId(oblId)) {
                        Profiling.addObligationId(oblId);
                        Executor.writeFeatureVector(bObl, wr);
                        Executor.writeObligation(bObl);
                    }
                }
            } catch (final IOException e) {
                System.err.println("Could not open \"profiling\" Writer");
            }
        }
    }

    /**
     * logs some PROFILING output <br>
     * prefix \t obligation \t name \t starttime \t cputime \t walltime \t
     * \t result \t parameter
     * @param prefix use Globals.PROFILE_PREFIX_*
     * @param pos BasicObligationNode
     * @param name of processor or strategy
     * @param parameter of processor or strategy
     * @param startTime point of start
     * @param cpuTime used cpu-time
     * @param result of processor or strategy
     * @param writer to write something
     * @throws IOException the exeption that is thrown when io goes wrong
     */
    static void logProfile(final String prefix,
        final BasicObligationNode pos,
        final String name,
        final Object parameter,
        final long startTime,
        final long cpuTime,
        final ExecutableStrategy result,
        final Writer writer) throws IOException {

        final long endTime = System.currentTimeMillis();
        // prefix Name startTime cpuTime wallTime strategyResult parameters

        writer.write(prefix);
        writer.write('\t');
        writer.write(pos.getBasicObligation().getId());
        writer.write('\t');
        writer.write(name);
        writer.write('\t');
        // startTime
        writer.write(Long.toString(startTime - Globals.startUpTime));
        writer.write('\t');
        writer.write(Long.toString(cpuTime));
        writer.write('\t');
        // wallTime
        writer.write(Long.toString(endTime - startTime));
        writer.write('\t');
        writer.write(result.toString());
        writer.write('\t');
        // see also ExecSimpleProfile
        writer.write(parameter.toString());
        writer.write('\n');
    }

    /**
     * write FeatureVector to Profiling.writer
     *
     * @param obl DefaultBasicobligation
     * @param writer to write something
     */
    private static void writeFeatureVector(final BasicObligation obl, final Writer writer) {
        if (obl instanceof HasFeatureVector<?>) {
            final HasFeatureVector<?> problem = (HasFeatureVector<?>) (obl);
            try {
                final FeatureVector<?> vector = problem.getFeatureVector();
                writer.write(Globals.PROFILE_PREFIX_FEATURE);
                writer.write("\t");
                writer.write(obl.getId());
                writer.write("\t");
                writer.write(vector.getType());
                writer.write("\t");
                writer.write(vector.getFeatures().toString());
                writer.write("\n");
            } catch (final IOException e) {
                System.err.println("Could not open \"profiling\" Writer");
            }
        }
    }

    /**
     * write externString to new Writer
     * @param obl to be written
     */
    private static void writeObligation(final BasicObligation obl) {
        final String name = "obligations/" + obl.getId();
        if (obl instanceof ExternUsable) {
            final ExternUsable problem = (ExternUsable) (obl);
            try {
                final Writer writer = AproveOutput.openWriter(name);
                writer.write(problem.toExternString());
                writer.close();
            } catch (final Exception e) {
                System.err.println(" write Obligation to " + name
                    + " -Writer failed");
            }
        }
    }

    /**
     * stop execution
     *
     * @param reason y u no go on?
     */
    public void stop(final String reason) {
        // This will also fire the abortion, see bottom of setResult().
        this.setResult(ResultFactory.aborted("STOP: " + reason));
    }

    /**
     * getter for the final time
     *
     * @return the final time
     */
    public long getFinalTime() {
        return this.clock.getMillisUsed();
    }

    /**
     * method to execute the obligation
     *
     * @throws AbortionException that will be thrown when aborting
     */
    protected void execute() throws AbortionException {
        final BasicObligation bObl = this.pos.getBasicObligation();
        if (Executor.LOG.isLoggable(Level.INFO)) {
            Executor.LOG.log(Level.INFO, System.nanoTime() / 1000000000 + " Started Exec." + this.executorNr
                + ", {0} on {1}...\n",
                    new Object[]{this.shortName, bObl.getId()});
        }
        final Result res = this.proc.process(bObl, this.pos, this.abortion, this.rti);
        this.setResult(res);
    }

    /**
     * getter for short name
     *
     * @return the short name
     */
    String getShortName() {
        return this.startUpTime / 1000 + "Exec. " + this.executorNr + ", " + this.shortName;
    }

    /**
     * getter for long name
     *
     * @return the long name
     */
    String getLongName() {
        return this.getShortName() + this.nameAddendum;
    }

    /**
     * another class for just running the execution
     *
     * @author thiemann
     */
    class Runner extends PooledJob {

        /**
         * create this runner
         *
         * @param abortionArg that should be thrown when aborting
         */
        public Runner(final Abortion abortionArg) {
            super(abortionArg);
        }

        @Override
        public String shortName() {
            return Executor.this.getShortName();
        }

        @Override
        public String longName() {
            return Executor.this.getLongName();
        }


        @Override
        protected void wrappedRun() throws AbortionException {
            Executor.this.execute();
        }


        @Override
        protected void onAborted(final AbortionException e) {
            Executor.this.setResult(ResultFactory.aborted(e));
        }

        @Override
        protected void onKilled(final ThreadDeath e) {
            Executor.this.setResult(ResultFactory.error(e));
        }

        @Override
        protected void onErrord(final Throwable e) {
            Executor.this.setResult(ResultFactory.error(e));
        }
    }
}
