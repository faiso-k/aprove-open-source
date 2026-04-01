package aprove.verification.dpframework.PATRSProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A PATRS is a triple (R, S, E).
 *
 * @author Stephan Falke
 * @version $Id$
 */

public final class PATRSProblem extends DefaultBasicObligation implements Immutable, Exportable, ExternUsable {

    private final ImmutableSet<PARule> R;
    private final ImmutableSet<Rule> S;
    private final ImmutableSet<Equation> E;

    /**
     * Describes function symbol signatures. An entry of the form
     * <code>a => [b,c,d]</code> matches with the signature
     * <code>a : b,c -> d</code>.
     */
    private final ImmutableMap<String, ImmutableList<String>> sortMap;

    private final int hashCode;

    /**
     * Creates a PATRS problem.
     * @param R - the rules with constraints
     * @param S - the constructor rules
     * @param E - the constructor equations
     */
    private PATRSProblem(ImmutableSet<PARule> R, ImmutableSet<Rule> S, ImmutableSet<Equation> E, ImmutableMap<String, ImmutableList<String>> sortMap) {
        super("PATRS", "PATRS");
        this.R = R;
        this.S = S;
        this.E = E;
        this.sortMap = sortMap;
        if (this.R != null && this.S != null && this.E != null) {
            this.hashCode = R.hashCode()*849033+S.hashCode()*8490+E.hashCode()*84903+8490213;
        } else {
            this.hashCode = 0;
        }
    }

    /**
     * Creates a new PATRSProblem for the given R, S, and E.
     *
     * @param sortMap Gives function symbol signatures. An entry of the form
     *         <code>a => [b,c,d]</code> matches with the signature
     *         <code>a : b,c -> d</code>.
     */
    public static PATRSProblem create(ImmutableSet<PARule> R, ImmutableSet<Rule> S, ImmutableSet<Equation> E, ImmutableMap<String, ImmutableList<String>> sortMap) {
        return new PATRSProblem(R, S, E, sortMap);
    }

    /**
     * Returns the set of DPs and a map from defined sumbols to tuple symbols.
     */
    public Pair<ImmutableSet<PARule>, Map<FunctionSymbol, FunctionSymbol>> getDPs() {
        synchronized(this) {
            Set<PARule> dps = new LinkedHashSet<PARule>();
            Set<FunctionSymbol> allfuns = new LinkedHashSet<FunctionSymbol>(this.getSignature());
            Set<FunctionSymbol> defs = this.getDefinedSymbols();
            Map<FunctionSymbol, FunctionSymbol> def_tup = new HashMap<FunctionSymbol, FunctionSymbol>();
            for (PARule rule : this.R) {
                Set<TRSFunctionApplication> calls = new LinkedHashSet<TRSFunctionApplication>();
                TRSFunctionApplication lhs = rule.getLeft();
                TRSTerm rhs = rule.getRight();
                ImmutableSet<PAConstraint> cond = rule.getConstraint();
                for (TRSFunctionApplication subterm : rhs.getNonVariableSubTerms()) {
                    FunctionSymbol root = subterm.getRootSymbol();
                    if (defs.contains(root)) {
                        calls.add(subterm);
                    }
                }
                if (calls.isEmpty()) {
                    continue;
                }
                FunctionSymbol tf = this.getTupleSymbol(lhs.getRootSymbol(), def_tup, allfuns);
                TRSFunctionApplication tlhs = TRSTerm.createFunctionApplication(tf, lhs.getArguments());
                for (TRSFunctionApplication call : calls) {
                    FunctionSymbol tg = this.getTupleSymbol(call.getRootSymbol(), def_tup, allfuns);
                    TRSFunctionApplication trhs = TRSTerm.createFunctionApplication(tg, call.getArguments());
                    dps.add(PARule.create(tlhs, trhs, cond));
                }
            }
            return new Pair<ImmutableSet<PARule>, Map<FunctionSymbol, FunctionSymbol>>(ImmutableCreator.create(dps), def_tup);
        }
    }

    private FunctionSymbol getTupleSymbol(FunctionSymbol f, Map<FunctionSymbol, FunctionSymbol> def_tup, Set<FunctionSymbol> allfuns) {
        FunctionSymbol tf = def_tup.get(f);
        if (tf == null) {
            String wishedName = f.getName().toUpperCase();
            int arity = f.getArity();
            int nr = 1;
            tf = FunctionSymbol.create(wishedName, arity);
            while (!allfuns.add(tf)) {
                tf = FunctionSymbol.create(wishedName + "^" + nr, arity);
                nr++;
            }
            def_tup.put(f, tf);
        }
        return tf;
    }

    public Set<FunctionSymbol> getDefinedSymbols() {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        for (PARule rule : this.R) {
            res.add(rule.getLeft().getRootSymbol());
        }
        return res;
    }

    public Set<FunctionSymbol> getDefinedSymbolsOfS() {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        for (Rule rule : this.S) {
            res.add(rule.getLeft().getRootSymbol());
        }
        return res;
    }

    public Set<FunctionSymbol> getRootSymbolsOfE() {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        for (Equation e : this.E) {
            res.add(((TRSFunctionApplication) e.getLeft()).getRootSymbol());
            res.add(((TRSFunctionApplication) e.getRight()).getRootSymbol());
        }
        return res;
    }

    /**
     * Returns the signature of R, S and E.
     */
    public synchronized ImmutableSet<FunctionSymbol> getSignature() {
        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.R);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.S));
        signature.addAll(CollectionUtils.getFunctionSymbols(this.E));
        return ImmutableCreator.create(signature);
    }

    public synchronized ImmutableMap<String, ImmutableList<String>> getSortMap() {
        return this.sortMap;
    }

    public ImmutableSet<PARule> getR() {
        return this.R;
    }

    public ImmutableSet<Rule> getS() {
        return this.S;
    }

    public ImmutableSet<Equation> getE() {
        return this.E;
    }

    @Override
    public boolean equals(Object oth) {
        if (this == oth) {
            return true;
        }
        if (oth == null) {
            return false;
        }
        if (oth.getClass() != this.getClass()) {
            return false;
        }
        PATRSProblem other = (PATRSProblem) oth;
        return this.R.equals(other.R) && this.S.equals(other.S) && this.E.equals(other.E);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public String export(Export_Util o) {
        StringBuffer s = new StringBuffer();
        s.append(o.export("PA-based rewrite system:"));
        s.append(o.cond_linebreak());
        if (this.R.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.R, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        if (this.S.isEmpty()) {
            s.append("S is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("S consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.S, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        if (this.E.isEmpty()) {
            s.append("E is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("E consists of the following equations:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.E, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        return s.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public String toITRSString() {
        StringBuilder res = new StringBuilder();
        // variables
        Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
        for (PARule rule : this.R) {
            vars.addAll(rule.getVariables());
        }
        res.append("(VAR ");
        for (TRSVariable v : vars) {
            res.append(v.getName() + " ");
        }
        res.append(")\n");
        // rules
        res.append("(RULES\n");
        for (PARule rule : this.R) {
            res.append(rule.toITRSString() + "\n");
        }
        res.append(")\n");
        return res.toString();
    }

    @Override
    public String externName() {
        return "patrs";
    }

    @Override
    public String toExternString() throws NotExternUsableInstanceException {
        for (Equation e : this.E) {
            if (!this.isPA((TRSFunctionApplication) e.getLeft())) {
                throw new NotExternUsableInstanceException("E contains non-PA equation");
            }
        }
        for (Rule r : this.S) {
            if (!this.isPA((TRSFunctionApplication) r.getLeft())) {
                throw new NotExternUsableInstanceException("S contains non-PA rule");
            }
        }

        StringBuilder s = new StringBuilder();
        /* Generate sorts */
        for (Map.Entry<String, ImmutableList<String>> sort : this.sortMap.entrySet()) {
            String fname = sort.getKey();
            if (fname.equals("+") || fname.equals("-") || fname.equals("0") || fname.equals("1")) {
                // don't generate line for PA symbols, otherwise the parser won't parse it
                continue;
            }
            s.append("[ ");
            s.append(sort.getKey());
            s.append(" : ");
            Iterator<String> it = sort.getValue().iterator();
            boolean first = true;
            /* produce s1, s2, s3 -> s4.
             * TODO: How to handle the case sort.getValue().size() == 1? */
            while (it.hasNext()) {
                String next = it.next();
                if (!it.hasNext()) {
                    s.append(" -> ");
                } else if (first) {
                    first = false;
                } else {
                    s.append(", ");
                }
                s.append(next);
            }
            s.append(" ]\n");
        }
        s.append('\n');

        /* Generate R */
        for (PARule r : this.R) {
            s.append(r.getLeft());
            s.append(" -> ");
            s.append(r.getRight());
            ImmutableSet<PAConstraint> constraints = r.getConstraint();
            if (constraints != null && !constraints.isEmpty()) {
                s.append(" [ ");
                boolean first = true;
                for (PAConstraint c : r.getConstraint()) {
                    if (first) {
                        first = false;
                    } else {
                        s.append(" /\\ ");
                    }
                    s.append(c);
                }
                s.append(" ]");
            }
            s.append('\n');
        }

        return s.toString();
    }

    private boolean isPA(TRSFunctionApplication t) {
        String fname = t.getRootSymbol().getName();
        return fname.equals("-") || fname.equals("+") || fname.equals("0") || fname.equals("1");
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "patrs";
    }
}
