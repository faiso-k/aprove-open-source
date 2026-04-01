package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.UserStrategies.*;


public class ExecCombineSequential extends ExecCombine {

    private ExecutableStrategy first;
    private boolean finishedSubstrategyWithSuccess = false;

    public ExecCombineSequential(List<ExecutableStrategy> strategies, RuntimeInformation rti) {
        super(strategies, rti, new Combine.Options());
        this.first = this.strategies.isEmpty() ? null : this.strategies.remove(0);
    }

    public ExecCombineSequential(Collection<UserStrategy> exStrs, BasicObligationNode pos, RuntimeInformation rti, Combine.Options options) {
        super(new LinkedList<>(), rti, options);
        for(UserStrategy userStr : exStrs) {
            this.strategies.add(userStr.getExecutableStrategy(pos, rti));
        }
        this.first = this.strategies.isEmpty() ? null : this.strategies.remove(0);
        this.pos = pos;
    }

    @Override
    ExecutableStrategy exec() {
        if (first != null) {
            if (!first.isNormal()) {
                ExecutableStrategy str = first.exec();
                if (str == null) {
                    return null;
                } else {
                    this.first = str;
                    return this;
                }
            } else {
                if (first.isFail()) {
                    this.first = this.strategies.isEmpty() ? null : this.strategies.remove(0);
                    return this;
                } else {
                    finishedSubstrategyWithSuccess = true;
                    Success succ = (Success) first;
                    this.positions.addAll(succ.getPositions());
                    if (this.strategies.isEmpty() || canBeAborted()) {
                        this.first = null;
                    } else {
                        this.first = this.strategies.remove(0);
                    }
                    return this;
                }
            }
        } else {
            if (!finishedSubstrategyWithSuccess) {
                return new Fail("All substrategies of Combine() failed");
            } else {
                return new Success(this.positions);
            }
        }
    }

    @Override
    void stop(String reason) {
        if (first != null) {
            this.first.stop(reason);
        }
    }

    @Override
    public String toString() {
        String res = "ECombineS(";
        boolean first;
        if (this.first == null) {
            first = true;
        } else {
            res += this.first;
            first = false;
        }
        for (ExecutableStrategy s : this.strategies) {
            if (first) {
                first = false;                
            } else {
                res += ", ";
            }
            res += s;
        }
        if (!first) {
            res += ", ";
        }
        res += "{";
        first = true;
        for (BasicObligationNode o : this.positions) {
            if (first) {
                first = false;
            } else {
                res += ",";
            }
            res += "someObl";
        }
        return res +"})";
    }

}
