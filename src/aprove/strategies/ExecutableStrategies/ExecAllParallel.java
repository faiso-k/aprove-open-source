package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.prooftree.Obligations.*;


public class ExecAllParallel extends ExecutableStrategy {

    private final List<ExecutableStrategy> strategies;
    private final Set<BasicObligationNode> positions;
    
    public ExecAllParallel(List<ExecutableStrategy> strategies, RuntimeInformation rti) {
        super(rti);        
        this.strategies = new LinkedList<ExecutableStrategy>(strategies);
        this.positions = new LinkedHashSet<BasicObligationNode>();
    }    
    
    @Override
    ExecutableStrategy exec() {
        if (this.strategies.isEmpty()) {
            return new Success(this.positions);
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
                        this.stop("All failed");
                        return new Fail("All() encountered Fail", (Fail) str);
                    } else {
                        Success succ = (Success) str;
                        this.positions.addAll(succ.getPositions());
                        strIter.remove();
                        change = true;
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
        String res = "EAllP(";
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
