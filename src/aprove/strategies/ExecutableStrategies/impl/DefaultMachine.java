package aprove.strategies.ExecutableStrategies.impl;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;

public class DefaultMachine implements Machine, Runnable {
    /*
     * Implementation note:
     *
     * This class has several Cmd* classes.
     * To ensure consistency of strategy execution, and consistency
     * of the proof tree, these MUST only be run from
     * the machine thread (see DefaultMachine.run().)
     *
     * Also, any operation on strategy or any mutating operation
     * on the proof tree MUST be done from this thread.
     * Allocating a new ObligationNode inside a processor is OK,
     * adding children to a new node is also OK, as long as it
     * is not attached to the main proof tree yet.
     */

    private static final Logger log = Logger.getAnonymousLogger();

    private static final Level logLevel = Level.FINE;
    private static final VariableStrategy theMainStrategy = new VariableStrategy("main");

    /* Fields accessible to other threads */
    private final AtomicInteger strNr;
    private final BlockingQueue<Runnable> commandQueue;
    private final Thread machineThread;

    /* Fields only used from inside machine thread */
    private final Map<Integer, Entry> running;

    public DefaultMachine() {
        this.strNr = new AtomicInteger(0);
        this.commandQueue = new LinkedBlockingQueue<Runnable>();

        // Since this map must only be accessed from the machine thread anyway,
        // no synchronization is necessary.
        this.running = new LinkedHashMap<Integer, Entry>();

        this.machineThread = new Thread(this);
        this.machineThread.setName("DefaultMachine");
        this.machineThread.setPriority(Thread.NORM_PRIORITY + 1);
        this.machineThread.setDaemon(true);
        this.machineThread.start();
    }

    @Override
    public StrategyExecutionHandle start(
        final UserStrategy strategy,
        final StrategyProgram program,
        final List<BasicObligationNode> positions,
        final Map<Metadata, Object> metadata)
    {
        return this.doStart(strategy, program, positions, metadata, null, true);
    }

    @Override
    public StrategyExecutionHandle startSubMachine(
        final UserStrategy strategy,
        final StrategyProgram program,
        final BasicObligationNode position,
        final Map<Metadata, Object> metadata,
        final List<Clock> clocks,
        final boolean checkProofs)
    {
        if (clocks == null) {
            throw new NullPointerException("no clocks");
        }
        final List<BasicObligationNode> positions = Collections.singletonList(position);
        return this.doStart(strategy, program, positions, metadata, clocks, checkProofs);
    }

    @Override
    public StrategyExecutionHandle startSubMachine(
        final UserStrategy strategy,
        final StrategyProgram program,
        final List<BasicObligationNode> positions,
        final Map<Metadata, Object> metadata,
        final List<Clock> clocks,
        final boolean checkProofs)
    {
        if (clocks == null) {
            throw new NullPointerException("no clocks");
        }
        return this.doStart(strategy, program, positions, metadata, clocks, checkProofs);
    }

    private StrategyExecutionHandle doStart(
        UserStrategy strategy,
        final StrategyProgram program,
        final List<BasicObligationNode> positions,
        final Map<Metadata, Object> metadata,
        final List<Clock> clocks,
        final boolean checkProofs)
    {

        if (strategy == null) {
            strategy = DefaultMachine.theMainStrategy;
        }

        final Integer nr = this.strNr.incrementAndGet();
        final Handle handle = new Handle(this, nr);

        final RuntimeState state = new RuntimeState(this, nr, program, metadata);
        RuntimeInformation rti;
        if (clocks == null) {
            rti = RuntimeImplementation.createInitial(state, checkProofs);
        } else {
            rti = RuntimeImplementation.createBelow(clocks, state, checkProofs);
        }

        ExecutableStrategy str;
        if (positions.size() == 1) {
            str = strategy.getExecutableStrategy(positions.get(0), rti);
        } else {
            //  construct the strategy
            final List<ExecutableStrategy> strategies = new ArrayList<ExecutableStrategy>(positions.size());
            for (final BasicObligationNode position : positions) {
                strategies.add(strategy.getExecutableStrategy(position, rti));
            }

            str = new ExecAllSequential(strategies, rti);
        }

        // create
        final Entry entry = new Entry(nr, handle, new StrategyRoot(str));
        this.putCommand(new CmdNew(entry));

        return handle;
    }

    void execute(final Integer nr) {
        this.putCommand(new CmdExec(nr));
    }

    void stop(final Integer nr, final String reason) {
        this.putCommand(new CmdStop(nr, reason));
    }

    @Override
    public void stopAll(final String reason) {
        this.putCommand(new CmdStopAll(reason));
    }

    private void putCommand(final Runnable command) {
        this.commandQueue.add(command);
    }

    /* ===== from here on we are inside the machine thread ===== */

    @Override
    public void run() {
        while (true) {
            Runnable command;

            try {
                command = this.commandQueue.take();
            } catch (final InterruptedException e) {
                continue; // TODO - really continue here on interrupt?
            }

            command.run();
        }
    }

    private class CmdNew implements Runnable {
        private final Entry entry;

        private CmdNew(final Entry entry) {
            this.entry = entry;
        }

        @Override
        public void run() {
            DefaultMachine.this.mustBeMachine();

            if (DefaultMachine.log.isLoggable(DefaultMachine.logLevel)) {
                DefaultMachine.log.log(DefaultMachine.logLevel, "Machine: started new strategy " + this.entry.id + ": " + this.entry.strat + ".\n");
            }

            final Entry old = DefaultMachine.this.running.put(this.entry.id, this.entry);

            if (Globals.useAssertions) {
                assert (old == null);
            }

            // and start running the new strategy
            DefaultMachine.this.putCommand(new CmdExec(this.entry.id));
        }
    }

    private class CmdExec implements Runnable {
        private final Integer nr;

        private CmdExec(final Integer nr) {
            this.nr = nr;
        }

        @Override
        public void run() {
            DefaultMachine.this.mustBeMachine();

            final Entry entry = DefaultMachine.this.running.get(this.nr);

            if (entry == null) {
                // Already stopped? Oh well, nothing to do then.
                return;
            }

            final StrategyRoot root = entry.strat;
            final ExecutableStrategy str = root.getExStr();
            if (str.isNormal()) {
                if (DefaultMachine.log.isLoggable(DefaultMachine.logLevel)) {
                    String result;
                    if (str.isFail()) {
                        result = "(Failure)";
                    } else if (((Success) str).getPositions().size() == 0) {
                        result = "(Success)";
                    } else {
                        result = "(Success [unfinished])";
                    }
                    DefaultMachine.log
                        .log(DefaultMachine.logLevel, "Machine: strategy "
                            + this.nr
                            + " is evaluated to normal form "
                            + result
                            + ".\n");
                }

                DefaultMachine.this.running.remove(this.nr);
                entry.stopInternal("Normal form reached");
                return;
            }

            final boolean changed = root.evaluateOnce();
            if (changed) {
                if (DefaultMachine.log.isLoggable(DefaultMachine.logLevel)) {
                    DefaultMachine.log.log(DefaultMachine.logLevel, "Machine: evaluated " + this.nr + " to " + root.getExStr() + ".\n");
                }
                // And reschedule us - this way is slightly fairer than looping directly
                DefaultMachine.this.putCommand(this);
            }
        }
    }

    private class CmdStop implements Runnable {
        private final Integer nr;
        private final String reason;

        private CmdStop(final Integer nr, final String reason) {
            this.nr = nr;
            this.reason = reason;
        }

        @Override
        public void run() {
            DefaultMachine.this.mustBeMachine();

            final Entry entry = DefaultMachine.this.running.remove(this.nr);
            if (entry == null) {
                // Already stopped? Oh well, less work for me!
                return;
            }

            entry.stopInternal(this.reason);
        }
    }

    private class CmdStopAll implements Runnable {
        private final String reason;

        private CmdStopAll(final String reason) {
            this.reason = reason;
        }

        @Override
        public void run() {
            DefaultMachine.this.mustBeMachine();

            final Iterator<Entry> it = DefaultMachine.this.running.values().iterator();
            while (it.hasNext()) {
                final Entry entry = it.next();
                it.remove();
                entry.stopInternal(this.reason);
            }

            DefaultMachine.log.log(Level.INFO, "Machine: stopped all\n");
        }
    }

    private void mustBeMachine() {
        if (Globals.useAssertions) {
            assert (Thread.currentThread() == this.machineThread);
        }
    }

    private class Entry extends AbortionListener {
        private final Integer id;
        private final Handle handle;

        private final StrategyRoot strat;

        private Entry(final Integer id, final Handle handle, final StrategyRoot strat) {
            this.id = id;
            this.handle = handle;
            this.strat = strat;
        }

        void stopInternal(final String reason) {
            DefaultMachine.this.mustBeMachine();

            this.handle.setFinished(reason, this.strat.getExStr());
            this.strat.stop(reason);

            DefaultMachine.log.log(Level.INFO, "Machine: stopped " + this.id + " with reason " + reason + ".\n");
        }

        /* Beware: this method is called by other threads */
        @Override
        public void abortionFired(final Abortion source, final String reason) {
            DefaultMachine.this.stop(this.id, reason);
        }
    }

}
