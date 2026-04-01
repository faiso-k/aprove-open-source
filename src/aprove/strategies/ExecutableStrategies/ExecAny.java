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
public class ExecAny extends ExecutableStrategy {

    private final List<Pair<BasicObligationNode,ExecutableStrategy>> strategies;
    private final BasicObligationNode root;
    private final boolean workOnCopies;

    public ExecAny(Collection<UserStrategy> strategies, BasicObligationNode oblNode, RuntimeInformation rti) {
        super(rti);
        this.workOnCopies = Options.strategyWorksOnCopies;
        this.strategies = new Vector<Pair<BasicObligationNode,ExecutableStrategy>>(strategies.size());
        this.root = oblNode;
        for (UserStrategy str : strategies) {
            BasicObligationNode newNode = this.workOnCopies ? new BasicObligationNode(oblNode) : oblNode;
            //BasicObligationNode newNode = oblNode.maybeCopy();
            this.strategies.add(new Pair<BasicObligationNode, ExecutableStrategy>(newNode, str.getExecutableStrategy(newNode, rti)));
        }
    }

    public ExecAny(Collection<ExecutableStrategy> exStrs, RuntimeInformation rti) {
        super(rti);
        this.workOnCopies = false; // This means neither root nor the Pair's x are ever used
        this.root = null;
        this.strategies = new ArrayList<Pair<BasicObligationNode,ExecutableStrategy>>(exStrs.size());
        for(ExecutableStrategy exStr : exStrs) {
            this.strategies.add(new Pair<BasicObligationNode, ExecutableStrategy>(null, exStr));
        }
    }

    @Override
    ExecutableStrategy exec() {
        boolean change = false;
        Iterator<Pair<BasicObligationNode,ExecutableStrategy>> stratIter = this.strategies.iterator();
        while (stratIter.hasNext()) {
            Pair<BasicObligationNode, ExecutableStrategy> nextPair = stratIter.next();
            ExecutableStrategy str = nextPair.y;
            if (str.isNormal()) {
                if (str.isFail()) {
                    stratIter.remove();
                } else { // Success
                    this.stop("Any succeeded");
                    if (this.workOnCopies) {
                        this.root.merge(nextPair.x);
                    }
                    return str;
                }
            } else {
                str = str.exec();
                if (str != null) {
                    // Check for Fail / Success already, for speed.
                    if (! str.isNormal()) {
                        nextPair.y = str;
                        change = true;
                    } else {
                        if (str.isFail()) {
                            stratIter.remove();
                        } else { // Success
                            this.stop("Any succeeded");
                            if (this.workOnCopies) {
                                this.root.merge(nextPair.x);
                            }
                            return str;
                        }
                    }
                }
            }
        }

        if (change) {
            return this; // Call us again, we had some inner strategy change - must evaluate it again.
        } else if (this.strategies.size() == 0) {
            return new Fail("Empty Any()"); // Fail if we just dropped our last strategy...
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
        String res = "EAny(";
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

}
