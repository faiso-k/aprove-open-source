package aprove.verification.oldframework.Rewriting ;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;

/**
 *  A hash set of lightweight rules with some additional functionality.
 *  @author Stephan Falke
 *  @version $Id$
 */

public class LightweightRules extends LinkedHashSet<LightweightRule> {

    public static LightweightRules create() {
    return new LightweightRules();
    }

    public static LightweightRules create(Collection<Rule> R) {
    LightweightRules res = new LightweightRules();
    Iterator i = R.iterator();
    while(i.hasNext()) {
        res.add(LightweightRule.create((Rule)i.next()));
    }
    return res;
    }

    /** Returns the function symbols occuring in the rules contained in this
     * set.
     */
    public List getSignature() {
    Set sig = new LinkedHashSet();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        LightweightRule rule = (LightweightRule)i.next();
        sig.addAll(rule.getLeft().getFunctionSymbols());
        sig.addAll(rule.getRight().getFunctionSymbols());
    }
    List result = new Vector();
    i = sig.iterator();
    while(i.hasNext()) {
        result.add(((Symbol)i.next()).getName());
    }
    return result;
    }

    /** Returns some element of this set, <code>null</code> if the set is empty.
     */
    public LightweightRule getArbitraryElement() {
    Iterator i = this.iterator();
    if(i.hasNext()) {
        return (LightweightRule)i.next();
    }
    else {
        return null;
    }
    }

    /** Returns some element of this set with minimal lenght, <code>null</code> if the set is empty.
     */
    public LightweightRule getMinimalElement() {
    int min = Integer.MAX_VALUE;
    LightweightRule res = null;
    Iterator i = this.iterator();
    if(i.hasNext()) {
        LightweightRule rule = (LightweightRule)i.next();
        int len = rule.length();
        if(len < min) {
        min = len;
        res = rule;
        }
    }

    return res;
    }

    public LightweightRules deepcopy() {
    LightweightRules result = LightweightRules.create();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        result.add(((LightweightRule)i.next()).deepcopy());
    }
    return result;
    }

    public Collection<Rule> toRules() {
    Collection<Rule> result = new LinkedHashSet<Rule>();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        result.add(((LightweightRule)i.next()).toRule());
    }
    return result;
    }

    public LightweightEquations toLightweightEquations() {
    LightweightEquations result = LightweightEquations.create();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        result.add(((LightweightRule)i.next()).toLightweightEquation());
    }
    return result;
    }

    /** Normalize all right hand sides of rules and return a new set.
     */
    public LightweightRules normalizeRight(LightweightRules R) {
    LightweightRules result = LightweightRules.create();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        result.add(((LightweightRule)i.next()).normalizeRight(R));
    }
    return result;
    }

    /** Normalize all left hand sides of rules and return a new set.
     */
    public LightweightRules normalizeLeft(LightweightRules R) {
    LightweightRules result = LightweightRules.create();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        result.add(((LightweightRule)i.next()).normalizeLeft(R));
    }
    return result;
    }

    /** Returns a new set containing the rules whose left hand side is
     * reducible.
     */
    public LightweightRules leftReducible(LightweightRule r) {
    LightweightRules result = LightweightRules.create();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        LightweightRule rule = (LightweightRule)i.next();
        if(rule.isLeftReducible(r)) {
            result.add(rule);
        }
    }
    return result;
    }
}
