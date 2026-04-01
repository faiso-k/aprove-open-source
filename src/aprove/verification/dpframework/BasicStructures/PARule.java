package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * A PARule is standard rewrite rule together with a PAConstraint.
 *
 * @author Stephan Falke
 * @version $Id$
 */
public final class PARule implements Immutable, Exportable, HasFunctionSymbols, HasVariables, DOTStringAble {

    protected final TRSFunctionApplication l;
    protected final TRSTerm r;
    protected final ImmutableSet<PAConstraint> c;

    /**
     * creates a new PARule.
     * @param l - a non-variable term
     * @param r - a term with less variables then l
     * @param c - PAConstraints
     */
    private PARule(TRSFunctionApplication l, TRSTerm r, ImmutableSet<PAConstraint> c) {
        this.l = l;
        this.r = r;
        this.c = ImmutableCreator.create(c);
    }

    /**
     * creates a new rule
     * @param l
     * @param r
     * @param c
     */
    public static PARule create(TRSFunctionApplication l, TRSTerm r, ImmutableSet<PAConstraint> c) {
        return new PARule(l, r, c);
    }

    /**
     * returns the lhs
     */
    public TRSFunctionApplication getLeft() {
        return this.l;
    }

    /**
     * returns the rhs
     */
    public TRSTerm getRight() {
        return this.r;
    }

    /**
     * returns the constraint
     */
    public ImmutableSet<PAConstraint> getConstraint() {
        return this.c;
    }

    /**
     * returns the set of functionSymbols occurring in this rule.
     * the resulting set may be modified
     */
    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        this.l.collectFunctionSymbols(fs);
        this.r.collectFunctionSymbols(fs);
        return fs;
    }

    /**
     * returns the set of variables occurring in this rule
     */
    @Override
    public Set<TRSVariable> getVariables() {
        return this.l.getVariables();
    }

    /**
     * Converts a set of rules into a rule map.
     */
    public static Map<FunctionSymbol, Set<PARule>> getRuleMap(Iterable<PARule> rules) {
        Map<FunctionSymbol, Set<PARule>> ruleMap = new LinkedHashMap<FunctionSymbol, Set<PARule>>();
        for (PARule rule : rules) {
            FunctionSymbol f = rule.l.getRootSymbol();
            Set<PARule> fRules = ruleMap.get(f);
            if (fRules == null) {
                fRules = new LinkedHashSet<PARule>();
                ruleMap.put(f, fRules);
            }
            fRules.add(rule);
        }
        return ruleMap;
    }

    @Override
    public String export(Export_Util eu) {
        return this.l.export(eu) + " " + eu.rightarrow() + " " + this.r.export(eu) + eu.set(this.c, Export_Util.PACOND);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String toDOTString() {
        Export_Util eu = new PLAIN_Util();
        return this.l.export(eu) + " " + eu.rightarrow() + " " + this.r.export(eu) + eu.set(this.c, Export_Util.PACONDDOT);
    }

    public String toITRSString() {
        StringBuilder res = new StringBuilder();
        res.append(this.toITRSString(this.l));
        res.append(" -> ");
        res.append(this.toITRSString(this.r));
        if (!this.c.isEmpty()) {
            res.append(" :|: ");
            res.append(this.toITRSString(this.c));
        }
        return res.toString();
    }

    private String toITRSString(TRSTerm t) {
        if (t.isVariable()) {
            return ((TRSVariable) t).getName();
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            String fname = ft.getRootSymbol().getName();
            StringBuilder res = new StringBuilder();
            if (fname.equals("+")) {
                res.append("(");
                res.append(this.toITRSString(ft.getArgument(0)));
                res.append(")");
                res.append(" + ");
                res.append("(");
                res.append(this.toITRSString(ft.getArgument(1)));
                res.append(")");
            } else if (fname.equals("-")) {
                res.append("-(");
                res.append(this.toITRSString(ft.getArgument(0)));
                res.append(")");
            } else {
                res.append(fname);
                Iterator<? extends TRSTerm> i = ft.getArguments().iterator();
                if (i.hasNext()) {
                    res.append("(");
                    res.append(this.toITRSString(i.next()));
                    while (i.hasNext()) {
                        res.append(", ");
                        res.append(this.toITRSString(i.next()));
                    }
                    res.append(")");
                }
            }
            return res.toString();
        }
    }

    private String toITRSString(Collection<PAConstraint> cs) {
        Set<String> tmp = new LinkedHashSet<String>();
        for (PAConstraint c : cs) {
            tmp.add(this.toITRSString(c));
        }
        StringBuilder res = new StringBuilder();
        Iterator<String> i = tmp.iterator();
        if (i.hasNext()) {
            res.append(i.next());
            while (i.hasNext()) {
                res.append(" && ");
                res.append(i.next());
            }
        }
        return res.toString();
    }

    private String toITRSString(PAConstraint c) {
        String ls = this.toITRSString(c.getLeft());
        String rs = this.toITRSString(c.getRight());
        switch (c.getType()) {
        case GTR:
            return ls + " > " + rs;
        case GTREQ:
            return ls + " >= " + rs;
        default:
            return ls + " = " + rs;
        }
    }

    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (other == null) {
            return false;
        }
        if (other instanceof PARule) {
            PARule rule = (PARule) other;
            return this.l.equals(rule.l) && this.r.equals(rule.r) && this.c.equals(rule.c);
        }
        return false;
    }

}
