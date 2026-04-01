package aprove.verification.oldframework.Rewriting.Transformers;

import java.util.*;

/** Class to realize very simple formulas. They are either conjunctions or
 *  a conjuntion with an implication. Basicly they are horn-formulas.
 *  @author Christian Haselbach
 *  @version $Id$
 */

public class SimpleFormula<T,U> {

    public Vector<T> premise;
    public U conclusion;

    private SimpleFormula() {
    this.premise = new Vector<T>();
    this.conclusion = null;
    }

    public static SimpleFormula createConjunction() {
    return new SimpleFormula();
    }

    public static <V,W> SimpleFormula<V,W> createConjunction(V literal) {
    SimpleFormula<V,W> phi = new SimpleFormula<V,W>();
    phi.premise.add(literal);
    return phi;
    }

    public static <V,W> SimpleFormula<V,W> createImplication(W literal) {
    SimpleFormula<V,W> phi = new SimpleFormula<V,W>();
    phi.conclusion = literal;
    return phi;
    }

    public static <V,W> SimpleFormula<V,W> createConjunction(SimpleFormula<V,W> phi, V literal) {
    // phi must be a conjunction.
    if (phi.conclusion != null) {
        return null;
    }
    SimpleFormula<V,W> psi = new SimpleFormula<V,W>();
    psi.premise.addAll(phi.premise);
    psi.premise.add(literal);
    return psi;
    }

    public static <V,W> SimpleFormula<V,W> createImplication(SimpleFormula<V,W> phi, W literal) {
    // phi must be a conjunction.
    if (phi.conclusion != null) {
        return null;
    }
    SimpleFormula<V,W> psi = new SimpleFormula<V,W>();
    psi.premise.addAll(phi.premise);
    psi.conclusion = literal;
    return psi;
    }

    public boolean isFact() {
    return this.premise.isEmpty();
    }

    public boolean premiseContainsAny(Set<T> literals) {
    for (T literal : literals) {
        if (this.premise.contains(literal)) {
        return true;
        }
    }
    return false;
    }

    public boolean premiseContainedIn(Set<T> literals) {
        boolean result = true;
        for (T premLiteral : this.premise) {
            result = result & literals.contains(premLiteral);
        }
        return result;
    }

    public U getConclusion() {
    return this.conclusion;
    }

    @Override
    public String toString() {
    StringBuffer out = new StringBuffer();
    int n = this.premise.size()-1;
    for (int i=0; i<=n; i++) {
        out.append(this.premise.get(i).toString());
        if (i<n) {
        out.append(" & ");
        }
    }
    if (this.conclusion != null) {
        out.append(" -> "+this.conclusion);
    }
    return out.toString();
    }

    @Override
    public boolean equals(Object o) {
    if (!(o instanceof SimpleFormula)) {
        return false;
    }
    SimpleFormula psi = (SimpleFormula)o;
    if (!this.conclusion.equals(psi.conclusion)) {
        return false;
    }
    return this.premise.equals(psi.premise);
    }

    @Override
    public int hashCode() {
    return this.premise.hashCode()+this.conclusion.hashCode();
    }
}
