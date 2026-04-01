package aprove.verification.dpframework.Orders ;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *   Two objects of the same type in some Relation (GR/GE/EQ),
 *   representing a constraint.
 *
 *   @author Peter Schneider-Kamp
 *   @version $Id$
 */

public class Constraint<T> extends Triple<T,T,OrderRelation> {

    private Constraint(T left, T right, OrderRelation rel) {
        super(left, right, rel);
        assert(rel == OrderRelation.GR || rel == OrderRelation.GE || rel == OrderRelation.EQ);
    }

    public static <U> Constraint<U> create(U left, U right, OrderRelation rel) {
        return new Constraint<U>(left, right, rel);
    }

    public T getLeft() {
        return this.x;
    }

    public T getRight() {
        return this.y;
    }

    public OrderRelation getType() {
        return this.z;
    }

    public static Set<Constraint<TRSTerm>> fromRules(Iterable<? extends GeneralizedRule> rules, OrderRelation rel) {
        Set<Constraint<TRSTerm>> cs = new LinkedHashSet<Constraint<TRSTerm>>();
        for (GeneralizedRule rule : rules) {
            cs.add(new Constraint<TRSTerm>(rule.getLeft(), rule.getRight(), rel));
        }
        return cs;
    }

    /**
     * Do the same as fromRules, but return the constraint as if the variables
     * were named x_i.
     * @param rules The rules to generate the constraint from.
     * @param rel The relation of the constraints.
     * @return Term constraints for the given rules.
     */
    public static Set<Constraint<TRSTerm>> fromRulesinStandardRepresentation(
            final Iterable<? extends GeneralizedRule> rules,
            final OrderRelation rel) {
        Set<Constraint<TRSTerm>> cs = new LinkedHashSet<Constraint<TRSTerm>>();
        for (GeneralizedRule rule : rules) {
            cs.add(new Constraint<TRSTerm>(
                    rule.getLhsInStandardRepresentation(),
                    rule.getRhsInStandardRepresentation(), rel));
        }
        return cs;
    }

    public static Constraint<TRSTerm> fromTerms(TRSTerm lhs, TRSTerm rhs, OrderRelation rel) {
        return new Constraint<TRSTerm>(lhs, rhs, rel);
    }

    public static Constraint<TRSTerm> fromRule(GeneralizedRule rule, OrderRelation rel) {
        return new Constraint<TRSTerm>(rule.getLeft(), rule.getRight(), rel);
    }

    public static Set<Constraint<TRSTerm>> fromEquations(Set<Equation> eqns) {
        Set<Constraint<TRSTerm>> cs = new LinkedHashSet<Constraint<TRSTerm>>();
        for (Equation eqn : eqns) {
            cs.add(new Constraint<TRSTerm>(eqn.getLeft(), eqn.getRight(), OrderRelation.EQ));
        }
        return cs;
    }

    public static Set<Constraint<TRSTerm>> fromPairsOfTerms(Set<Pair<TRSTerm,TRSTerm>> rules, OrderRelation rel) {
        Set<Constraint<TRSTerm>> cs = new LinkedHashSet<Constraint<TRSTerm>>();
        for (Pair<TRSTerm,TRSTerm> rule : rules) {
            cs.add(new Constraint<TRSTerm>(rule.x, rule.y, rel));
        }
        return cs;
    }

    public static Set<FunctionSymbol> getFunctionSymbols(Collection<Constraint<TRSTerm>> cs) {
        Set<FunctionSymbol> symbols;
        symbols = new LinkedHashSet<FunctionSymbol>();
        for (Constraint<TRSTerm> constraint : cs) {
            symbols.addAll(constraint.getLeft().getFunctionSymbols());
            symbols.addAll(constraint.getRight().getFunctionSymbols());
        }
        return symbols;
    }

    public static Set<TRSVariable> getVariables(Collection<Constraint<TRSTerm>> cs) {
        Set<TRSVariable> symbols;
        symbols = new LinkedHashSet<TRSVariable>();
        for (Constraint<TRSTerm> constraint : cs) {
            symbols.addAll(constraint.getLeft().getVariables());
            symbols.addAll(constraint.getRight().getVariables());
        }
        return symbols;
    }

    public static Set<String> getSignature(Collection<Constraint<TRSTerm>> cs) {
        Set<String> sig;
        sig = new LinkedHashSet<String>();
        for (FunctionSymbol fSym : Constraint.getFunctionSymbols(cs)) {
            sig.add(fSym.getName());
        }
        return sig;
    }
}
