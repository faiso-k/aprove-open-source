package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public class ExecAnyDelay extends ExecutableStrategy {

    private final long delay;
    private final List<Pair<BasicObligationNode,ExecutableStrategy>> strategies;
    private final BasicObligationNode root;
    private final boolean workOnCopies;
    private final Thread delayThread;

    private boolean startOther;

    public ExecAnyDelay(long delay, Collection<UserStrategy> strategies, BasicObligationNode oblNode, RuntimeInformation rti) {
        super(rti);
        this.delay = delay;
        this.workOnCopies = Options.strategyWorksOnCopies;
        this.strategies = new ArrayList<Pair<BasicObligationNode,ExecutableStrategy>>(strategies.size());
        this.root = oblNode;
        for (UserStrategy str : strategies) {
            BasicObligationNode newNode = this.workOnCopies ? new BasicObligationNode(oblNode) : oblNode;
            this.strategies.add(new Pair<BasicObligationNode, ExecutableStrategy>(newNode, str.getExecutableStrategy(newNode, rti)));
        }

        this.startOther = false; // Set to true when the delay expires normally
        this.delayThread = new Thread(new AnyDelayTimer(), "delay thread");
        this.delayThread.start();
    }

    @Override
    ExecutableStrategy exec() {
        if (this.strategies.size() == 0) {
            this.delayThread.interrupt();
            return new Fail("AnyDelay() empty");
        }

        boolean change = false;
        Iterator<Pair<BasicObligationNode,ExecutableStrategy>> stratIter = this.strategies.iterator();
        boolean first = true;
        // Poke at least the first entry, and the other ones if our delay expired
        while (stratIter.hasNext() && (first || this.startOther)) {
            first = false;
            Pair<BasicObligationNode, ExecutableStrategy> nextPair = stratIter.next();
            ExecutableStrategy str = nextPair.y;
            if (str.isNormal()) {
                if (str.isFail()) {
                    change = true;
                    stratIter.remove();
                    this.delayThread.interrupt();
                    this.startOther = true;
                    this.delayDone();
                } else {
                    this.stop("AnyDelay succeeded");
                    if (this.workOnCopies) {
                        this.root.merge(nextPair.x);
                    }
                    this.delayThread.interrupt();
                    return str;
                }
            } else {
                ExecutableStrategy oldStr = str;
                str = str.exec();
                if (str != null) {
                    change = true;
                    if (str != oldStr) {
                        nextPair.y = str;
                    }
                }
            }
        }
        if (change) {
            return this;
        } else {
            return null;
        }
    }

    @Override
    void stop(String reason) {
        for (Pair<BasicObligationNode, ExecutableStrategy> str : this.strategies) {
            str.y.stop(reason);
        }
    }

    @Override
    public String toString() {
        String res = "EAnyDelay(" + this.delay + ", ";
        boolean first = true;
        for (Pair<BasicObligationNode,ExecutableStrategy> s : this.strategies) {
            if (first) {
                first = false;
            } else {
                res += ", ";
            }
            res += s.y;
        }
        return res +")";
    }

    private void delayDone() {
        this.startOther = true;
        this.rti.execute();
    }

    private class AnyDelayTimer implements Runnable {

        @Override
        public void run() {
            try {
                Thread.sleep(ExecAnyDelay.this.delay);
                ExecAnyDelay.this.delayDone();
            } catch (InterruptedException e) {
                // Ignore, but don't wake up startOther then.
            }
        }

    }

}
