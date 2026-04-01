package aprove.verification.dpframework.PATRSProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * A CSPATRS is a quadruple (R, S, E, mu).
 *
 * @author Stephan Falke
 * @version $Id$
 */

public final class CSPATRSProblem extends DefaultBasicObligation implements Immutable, Exportable {

    private final ImmutableSet<PARule> R;
    private final ImmutableSet<Rule> S;
    private final ImmutableSet<Equation> E;
    private final ImmutableMap<String, ImmutableSet<Integer>> mu;

    /**
     * Describes function symbol signatures. An entry of the form
     * <code>a => [b,c,d]</code> matches with the signature
     * <code>a : b,c -> d</code>.
     */
    private final ImmutableMap<String, ImmutableList<String>> sortMap;

    private final int hashCode;

    /**
     * Creates a CSPATRS problem.
     * @param R - the rules with constraints
     * @param S - the constructor rules
     * @param E - the constructor equations
     * @param mu - the replacement map
     */
    private CSPATRSProblem(ImmutableSet<PARule> R, ImmutableSet<Rule> S, ImmutableSet<Equation> E, ImmutableMap<String, ImmutableList<String>> sortMap, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        super("CSPATRS", "CSPATRS");
        this.R = R;
        this.S = S;
        this.E = E;
        this.sortMap = sortMap;
        this.mu = mu;
        if (this.R != null && this.S != null && this.E != null && this.mu != null) {
            this.hashCode = R.hashCode()*849033+S.hashCode()*8490+E.hashCode()*84903+8490213;
        } else {
            this.hashCode = 0;
        }
    }

    /**
     * Creates a new CSPATRSProblem for the given R, S, and E, mu.
     *
     * @param sortMap Gives function symbol signatures. An entry of the form
     *         <code>a => [b,c,d]</code> matches with the signature
     *         <code>a : b,c -> d</code>.
     */
    public static CSPATRSProblem create(ImmutableSet<PARule> R, ImmutableSet<Rule> S, ImmutableSet<Equation> E, ImmutableMap<String, ImmutableList<String>> sortMap, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        return new CSPATRSProblem(R, S, E, sortMap, mu);
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

    /**
     * Returns the signature of S and E.
     */
    public synchronized ImmutableSet<FunctionSymbol> getSignatureSE() {
        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.S);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.E));
        return ImmutableCreator.create(signature);
    }

    public synchronized ImmutableMap<String, ImmutableList<String>> getSortMap() {
        return this.sortMap;
    }

    public synchronized ImmutableMap<String, ImmutableSet<Integer>> getMu() {
        return this.mu;
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
        CSPATRSProblem other = (CSPATRSProblem) oth;
        return this.R.equals(other.R) && this.S.equals(other.S) && this.E.equals(other.E) && this.mu.equals(other.mu);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public String export(Export_Util o) {
        StringBuffer s = new StringBuffer();
        s.append(o.export("Context-sensitive PA-based rewrite system:"));
        s.append(o.cond_linebreak());
        s.append(o.export("The replacement map contains the following entries:"));
        s.append(o.cond_linebreak());
        Set<String> tmp = new LinkedHashSet<String>();
        for (Map.Entry<String, ? extends Set<Integer>> repEntry : this.mu.entrySet()) {
            Set<Integer> repl = repEntry.getValue();
            ArrayList<Integer> shiftSet = new ArrayList<Integer>(repl.size());
            for (Integer i : repl) {
                shiftSet.add(i + 1);
            }
            tmp.add(repEntry.getKey() + ": " + o.set(shiftSet, Export_Util.SIMPLESET));
        }
        s.append(o.set(tmp, Export_Util.RULES));
        s.append(o.linebreak());
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

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "cspatrs";
    }
}
