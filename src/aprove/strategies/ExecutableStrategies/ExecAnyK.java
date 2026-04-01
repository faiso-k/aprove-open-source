package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Execute an any. All given strategies are started in parallel. The first successful result
 * is used further. If all strategies fail the any results in a fail, too.
 * If started with low priority, we only start the strategies up to the thread limit. Remaining
 * strategies are ignored.
 */
public class ExecAnyK extends ExecutableStrategy {

    private final int k;
    private final List<Pair<BasicObligationNode,ExecutableStrategy>> strategies;
    private final BasicObligationNode root;
    private final boolean workOnCopies;

    public ExecAnyK(final int k, final Collection<UserStrategy> strategies, final BasicObligationNode oblNode, final RuntimeInformation rti) {
        super(rti);
        this.workOnCopies = Options.strategyWorksOnCopies;
        this.k = k;
        this.strategies = new Vector<Pair<BasicObligationNode,ExecutableStrategy>>(strategies.size());
        this.root = oblNode;
        for (final UserStrategy str : strategies) {
            final BasicObligationNode newNode = this.workOnCopies ? new BasicObligationNode(oblNode) : oblNode;
            //BasicObligationNode newNode = oblNode.maybeCopy();
            this.strategies.add(new Pair<BasicObligationNode, ExecutableStrategy>(newNode, str.getExecutableStrategy(newNode, rti)));
        }
    }

    public ExecAnyK(final int k, final Collection<ExecutableStrategy> exStrs, final RuntimeInformation rti) {
        super(rti);
        this.workOnCopies = false; // This means neither root nor the Pair's x are ever used
        this.root = null;
        this.k = k;
        this.strategies = new ArrayList<Pair<BasicObligationNode,ExecutableStrategy>>(exStrs.size());
        for(final ExecutableStrategy exStr : exStrs) {
            this.strategies.add(new Pair<BasicObligationNode, ExecutableStrategy>(null, exStr));
        }
    }

    @Override
    synchronized ExecutableStrategy exec() {
        boolean change = false;
        boolean sleepingExecution = false;

        final Iterator<Pair<BasicObligationNode,ExecutableStrategy>> executingIterator = this.strategies.iterator();

        int remainingK = this.k;

        while (executingIterator.hasNext()) {
            final Pair<BasicObligationNode, ExecutableStrategy> nextPair = executingIterator.next();
            ExecutableStrategy str = nextPair.y;
            if (str.isNormal()) {
                if (str.isFail()) {
                    executingIterator.remove();
                } else { // Success
                    this.stop("Any succeeded");
                    if (this.workOnCopies) {
                        this.root.merge(nextPair.x);
                    }
                    return str;
                }
            } else if (remainingK > 0) {
                str = str.exec();
                if (str != null) {
                    // Check for Fail / Success already, for speed.
                    if (! str.isNormal()) {
                        nextPair.y = str;
                        change = true;
                    } else {
                        if (str.isFail()) {
                            executingIterator.remove();
                        } else { // Success
                            this.stop("Any succeeded");
                            if (this.workOnCopies) {
                                this.root.merge(nextPair.x);
                            }
                            return str;
                        }
                    }
                } else {
                    remainingK --;
                }
            } else {
                sleepingExecution = true;
            }
        }

        if (change) {
            return this; // Call us again, we are not finished or had some inner strategy change - must evaluate it again.
        } else if (this.strategies.size() == 0) {
            return new Fail("Empty Any()"); // Fail if we just dropped our last strategy...
        } else {
            return null;
        }
    }

    @Override
    void stop(final String reason) {
        for (final Pair<BasicObligationNode, ExecutableStrategy> str : this.strategies) {
            str.y.stop(reason);
        }
    }

    @Override
    public String toString() {
        String res = "EAnyK(";
        boolean first = true;
        for (final Pair<BasicObligationNode,ExecutableStrategy> s : this.strategies) {
            if (first) {
                first = false;
            } else {
                res += ", ";
            }
            res += s.y;
        }
        return res +")";
    }

}
