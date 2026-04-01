package aprove.verification.dpframework;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;


/**
 * A processor that produces several Results until one is successful.
 *
 * Implement {@link #buildStateIterator()} to return an Iterator over whatever
 * you want to use as state.
 *
 * Then, implement {@link #processOnce(T, BasicObligation, BasicObligationNode, Abortion, RuntimeInformation)},
 * which will be given each object from the state object in turn.
 * As soon as a Result leads to Success, this stops.
 *
 * For best results, create a Result with a strategy inside, so that result is
 * only kept if the enclosed strategy also returns Success.
 */
public abstract class IterativeProcessor<T> implements Processor {
    @Override
    public final Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) {

        IterativeProcWinder winder = new IterativeProcWinder(this.buildStateIterator());
        ExecutableStrategy sResult = this.myStrategy(oblNode, rti, winder);

        return ResultFactory.justANewStrategy(sResult);
    }

    protected abstract Iterator<T> buildStateIterator();

    public abstract Result processOnce(T state, BasicObligation obl,
            BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti);

    ExecProcessorStrategy myStrategy(BasicObligationNode oblNode,
            RuntimeInformation rti, IterativeProcWinder winder) {
        return new ExecProcessorStrategy(
                winder, oblNode, rti, "internal", "(iterative Processor)");
    }

    private class IterativeProcWinder implements Processor {
        private final Iterator<T> state;

        public IterativeProcWinder(Iterator<T> state) {
            this.state = state;
        }

        @Override
        public boolean isApplicable(BasicObligation obl) {
            return true;
        }

        @Override
        public Result process(BasicObligation obl, BasicObligationNode oblNode,
                Abortion aborter, RuntimeInformation rti)
        throws AbortionException {
            if (! this.state.hasNext()) {
                return ResultFactory.unsuccessful("IterativeProcessor ended");
            }

            T stateObj = this.state.next();
            Result initial = IterativeProcessor.this.processOnce(stateObj, obl, oblNode, aborter, rti);

            ExecutableStrategy attempt = new ExecResult(rti, oblNode, initial);
            ExecutableStrategy iterate = IterativeProcessor.this.myStrategy(oblNode, rti, this);

            ExecutableStrategy exStr = ExecFirst.createFromExec(Arrays.asList(attempt, iterate), oblNode, rti);
            return ResultFactory.justANewStrategy(exStr);
        }
    }
}
