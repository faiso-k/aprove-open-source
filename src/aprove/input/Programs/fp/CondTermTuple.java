package aprove.input.Programs.fp;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;

/**
 * A class that represents one tuple of a conditional term.
 * @author Christian Haselbach
 */

class CondTermTuple {
    public Set<Rule> conds;
    public AlgebraTerm term;

    public CondTermTuple(AlgebraTerm t) {
    this.conds = new LinkedHashSet<Rule>();
    this.term = t;
    }

    public CondTermTuple() {
    this.conds = new LinkedHashSet<Rule>();
    this.term = null;
    }

    protected CondTermTuple(Set<Rule> co, AlgebraTerm t) {
    this.conds = co;
    this.term = t;
    }

    public void set_term(AlgebraTerm t) {
    this.term = t;
    }

    /**
     * Creates a new CondTermTuple by merging this and a given
     * CondTermTuple c and adding the term of c as a rule that
     * has to evaluate to true to the conditions.
     */
    public CondTermTuple create_true(CondTermTuple c, AlgebraTerm cotrue) {
    Set<Rule> co = new LinkedHashSet<Rule>(c.conds);
    co.add(Rule.create(c.term, cotrue));
    co.addAll(this.conds);
    return new CondTermTuple(co, this.term);
    }

    /**
     * Creates a new CondTermTuple by merging this and a given
     * CondTermTuple c and adding the term of c as a rule that
     * has to evaluate to false to the conditions.
     */
    public CondTermTuple create_false(CondTermTuple c, AlgebraTerm cofalse) {
    Set<Rule> co = new LinkedHashSet<Rule>(c.conds);
    co.add(Rule.create(c.term, cofalse));
    co.addAll(this.conds);
    return new CondTermTuple(co, this.term);
    }

    /**
     * Creates a new CondTermTuple by merging this and a given
     * CondTermTuple c and adding the term of c as a rule that
     * has to evaluate to a given term to the conditions.
     */
    public CondTermTuple create(AlgebraTerm t, CondTermTuple c) {
    Set<Rule> co = new LinkedHashSet<Rule>(c.conds);
    co.add(Rule.create(c.term, t));
    co.addAll(this.conds);
    return new CondTermTuple(co, this.term);
    }

    /**
     * Creates a new CondTermTuple by merging this and a given
     * CondTermTuple c and adding the term of c as a rule that
     * has to evaluate to false to the conditions.
     */
    public CondTermTuple create(CondTermTuple c) {
    Set<Rule> co = new LinkedHashSet<Rule>(c.conds);
    co.addAll(this.conds);
    return new CondTermTuple(co, this.term);
    }

    /**
     * Merges the conditions of c into this CondTermTuple.
     */
    public void merge(CondTermTuple c) {
    this.conds.addAll(c.conds);
    }

    /**
     * Makes a rule out of this CondTermTuple and a given lhs.
     */
    public Rule get_rule(AlgebraTerm left) {
    return Rule.create(new Vector<Rule>(this.conds), left, this.term);
    }

    @Override
    public String toString() {
    return "("+this.conds+", "+this.term+")";
    }
}
