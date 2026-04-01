package aprove.verification.dpframework.BasicStructures.Matchbounds;


import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Helper class to match paths in a graph to rules.
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version $Id$
 */
public class MatchingRulesState {

    private Set<Rule> rules;
    private Map<FunctionSymbol, MatchingRulesState> successors;

    public MatchingRulesState() {

        this.rules = null;
        this.successors = new LinkedHashMap<FunctionSymbol, MatchingRulesState>();

    }

    private static final TRSVariable someVariable = TRSTerm.createVariable("foo");

    public static MatchingRulesState constructFromRules(Set<Rule> input) {

        MatchingRulesState start = new MatchingRulesState();

        for (Rule rule : input) {

            TRSTerm tmpTerm = rule.getLeft();
            MatchingRulesState tmpState = start;

            while (!tmpTerm.isVariable()) {
                TRSFunctionApplication f = (TRSFunctionApplication) tmpTerm;
                FunctionSymbol symbol = f.getRootSymbol();

                if (tmpState.hasSuccessor(symbol)) {
                    tmpState = tmpState.getSuccessor(symbol);
                } else {
                    MatchingRulesState succ = new MatchingRulesState();
                    tmpState = tmpState.addSuccessor(symbol, succ);
                }

                if (symbol.getArity() > 0) {
                    tmpTerm = f.getArgument(0);
                } else {
                    tmpTerm = MatchingRulesState.someVariable;
                }
            }

            tmpState.addRule(rule);
        }

        return start;
    }

    public MatchingRulesState addSuccessor(FunctionSymbol symbol, MatchingRulesState successor) {
        this.successors.put(symbol, successor);
        return successor;
    }

    public boolean hasRules() {
        return (this.rules != null);
    }

    public void addRule(Rule rule) {
        if (this.rules == null) {
            this.rules = new LinkedHashSet<Rule>();
        }
        this.rules.add(rule);
    }

    public Set<Rule> getRules() {
        return this.rules;
    }

    public boolean hasSuccessor(FunctionSymbol symbol) {
        return this.successors.containsKey(symbol);
    }

    public Set<FunctionSymbol> getPossibleSuccessors() {
        return this.successors.keySet();
    }

    public MatchingRulesState getSuccessor(FunctionSymbol symbol) {
        return this.successors.get(symbol);
    }

    @Override
    public String toString() {

        StringBuilder out = new StringBuilder();
        out.append('[');

        if (this.rules != null) {
            out.append(this.rules.toString());
        } else {
            out.append(" no rules ");
        }

        for (Map.Entry<FunctionSymbol, MatchingRulesState> entry : this.successors.entrySet()) {
            out.append("| ");
            out.append(entry.getKey());
            out.append(" -> ");
            out.append(entry.getValue());
        }

        out.append(']');
        return out.toString();

    }

}
