package aprove.verification.oldframework.LemmaDatabase.Index;

import java.util.*;

import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class IndexNode extends LinkedHashMap<IndexSymbol,IndexNode> {

    protected Pair<IndexSymbol,IndexNode>  parent;

    protected Set<Formula>  reachableFormulas;

    protected Set<Formula>  results;

    public IndexNode(IndexSymbol parentKey, IndexNode parent) {

        this.parent            = new Pair<IndexSymbol,IndexNode>(parentKey,parent);
        this.results           = new LinkedHashSet<Formula>();
        this.reachableFormulas = new LinkedHashSet<Formula>();

    }

    public boolean isLeaf() {
        return this.entrySet().isEmpty();
    }

    public void addResult(Formula formula) {
        this.results.add(formula);
    }

    public void removeResult(Formula formula) {
        this.results.remove(formula);
    }

    public IndexNode getParent() {
        return this.parent.y;
    }

    public IndexSymbol getParentKey() {
        return this.parent.x;
    }

    public int numberOfFormulas()    {
        return this.results.size();
    }

    public int numberOfChildren() {
        return this.size();
    }

    public Set<Formula> getReachableFormulas() {
        return new LinkedHashSet<Formula>(this.reachableFormulas);
    }

    public void addReachableFormula(Formula formula) {
        this.reachableFormulas.add(formula);
    }

    public void removeReachableFormula(Formula formula) {
        this.reachableFormulas.remove(formula);
    }

    public Set<Formula> getResults() {
        return new LinkedHashSet<Formula>(this.results);
    }

    @Override
    public String toString() {

        StringBuffer stringBuffer = new StringBuffer();

        for( Map.Entry<IndexSymbol,IndexNode> entry : this.entrySet()) {
            stringBuffer.append(entry.getKey());
            stringBuffer.append("\n\t");
            stringBuffer.append(entry.getValue());
        }

        return stringBuffer.toString();
    }
}
