package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.UserStrategies.*;

public class ExecSequence extends ExecutableStrategy {

    private ExecutableStrategy first;
    private final UserStrategy second;
    private final boolean parallel;

    public ExecSequence(ExecutableStrategy first, UserStrategy second, boolean parallel, RuntimeInformation rti) {
        super(rti);
        this.first = first;
        this.second = second;
        this.parallel = parallel;
    }

    @Override
    ExecutableStrategy exec() {
        if (!this.first.isNormal()) {
            ExecutableStrategy s = this.first.exec();
            if (s == null) {
                return null;
            } else {
                this.first = s;
                return this;
            }
        } else {
            if (this.first.isFail()) {
                return new Fail("Sequence failed", (Fail) this.first);
            } else {
                Success succ = (Success) this.first;
                List<BasicObligationNode> positions = succ.getPositions();
                Vector<ExecutableStrategy> strategies = new Vector<ExecutableStrategy>(positions.size());
                for (BasicObligationNode pos : positions) {
                    strategies.add(this.second.getExecutableStrategy(pos, this.rti));
                }
                if (strategies.size() == 1) {
                    return strategies.firstElement();
                } else {
                    if (this.parallel) {
                        return new ExecAllParallel(strategies, this.rti);
                    } else {
                        return new ExecAllSequential(strategies, this.rti);
                    }
                }
            }
        }
    }

    @Override
    void stop(String reason) {
        this.first.stop(reason);
    }

    @Override
    public String toString() {
        return "ESequence_"+(this.parallel ? "B" : "D")+"("+this.first+", "+this.second+")";
    }

}
