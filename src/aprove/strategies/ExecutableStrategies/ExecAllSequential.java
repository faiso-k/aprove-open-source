package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.prooftree.Obligations.*;

public class ExecAllSequential extends ExecutableStrategy {

    private final List<ExecutableStrategy> strategies;
    private final Set<BasicObligationNode> positions;
    private ExecutableStrategy first;
    
    public ExecAllSequential(List<ExecutableStrategy> strategies, RuntimeInformation rti) {
        super(rti);        
        this.strategies = new LinkedList<ExecutableStrategy>(strategies);
        this.first = this.strategies.isEmpty() ? null : this.strategies.remove(0);
        this.positions = new LinkedHashSet<BasicObligationNode>();
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
                    return new Fail("All() encountered Fail", (Fail) first);
                } else {
                    Success succ = (Success) first;
                    this.positions.addAll(succ.getPositions());
                    this.first = this.strategies.isEmpty() ? null : this.strategies.remove(0);
                    return this;
                }
            }
        } else {                 
            return new Success(this.positions);
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
        String res = "EAllS(";
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
