package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.UserStrategies.*;


public class ExecCombineParallel extends ExecCombine {

    private boolean finishedSubstrategyWithSuccess = false;

    public ExecCombineParallel(List<ExecutableStrategy> strategies, RuntimeInformation rti) {
        super(new LinkedList<>(strategies), rti, new Combine.Options());
    }

    public ExecCombineParallel(Collection<UserStrategy> exStrs, BasicObligationNode pos, RuntimeInformation rti, Combine.Options options) {
        super(new LinkedList<>(), rti, options);
        for(UserStrategy userStr : exStrs) {
            this.strategies.add(userStr.getExecutableStrategy(pos, rti));
        }
        this.pos = pos;
    }

    @Override
    ExecutableStrategy exec() {
        if (this.strategies.isEmpty()) {
            if (!finishedSubstrategyWithSuccess) {
                return new Fail("All substrategies of Combine() failed");
            } else {
                return new Success(this.positions);
            }
        } else {
            ListIterator<ExecutableStrategy> strIter = this.strategies.listIterator();
            boolean change = false;
            while (strIter.hasNext()) {
                ExecutableStrategy str = strIter.next();
                if (!str.isNormal()) {
                    ExecutableStrategy newStr = str.exec();
                    if (newStr != null) {
                        strIter.set(newStr);
                        change = true;
                    }
                } else {
                    if (str.isFail()) {
                        change = true;
                        strIter.remove();
                    } else {
                        finishedSubstrategyWithSuccess = true;
                        Success succ = (Success) str;
                        this.positions.addAll(succ.getPositions());
                        strIter.remove();
                        change = true;
                        if (canBeAborted()) {
                            for (ExecutableStrategy s: this.strategies) {
                                s.stop("found optimal solution");
                            }
                            return new Success(this.positions);
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
    }

    @Override
    void stop(String reason) {
        for (ExecutableStrategy str : this.strategies) {
            str.stop(reason);
        }
    }

    @Override
    public String toString() {
        String res = "ECombineP(";
        boolean first = true;
        for (ExecutableStrategy s : this.strategies) {
            if (first) {
                first = false;
            } else {
                res += ", ";
            }
            res += s;
        }
        if (first) {
            res += ", ";
        }
        res += "{";
        first = true;
        for (ObligationNode o : this.positions) {
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
