package aprove.verification.oldframework.ConditionalRewriting;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * Class for a conditional critical pair
 *
 * @author dickmeis
 * @version $Id$
 */

public class ConditionalCriticalPair {

    private AlgebraTerm l;
    private AlgebraTerm r;

    private Set<Rule> conditions;

    private Rule r1;
    private Rule r2;

    public ConditionalCriticalPair(AlgebraTerm l, AlgebraTerm r, Set<Rule> conditions, Rule r1, Rule r2){
        this.l = l.deepcopy();
        this.r = r.deepcopy();
        this.conditions = new HashSet<Rule>(conditions.size());
        for (Rule rule : conditions) {
            this.conditions.add(rule.deepcopy());
        }
        this.r1 = r1.deepcopy();
        this.r2 = r2.deepcopy();
    }

    @Override
    public String toString(){
        return("< " + this.l + ", " + this.r + ">  <== " + this.conditions + " build from rule " + this.r1 + " and rule " + this.r2 +"\n");
    }

    /**
     *
     * @return true if the terms are identical
     */
    public boolean isTrivial(){
        return this.l.equals(this.r);
    }

    /**
     * @return the conditions
     */
    public Set<Rule> getConditions() {
        return this.conditions;
    }

    /**
     * @return the left term
     */
    public AlgebraTerm getLeft() {
        return this.l;
    }

    /**
     * @return the right term
     */
    public AlgebraTerm getRight() {
        return this.r;
    }

}
