package aprove.verification.dpframework.PADPProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Represents a CSPADPProblem containing a CSPATRSProblem and a set of dependency pairs.
 *
 * @author Stephan Falke
 * @version $Id$
 */

public final class CSPADPProblem extends DefaultBasicObligation implements Immutable {

    private final ImmutableSet<PARule> P;
    private final CSPATRSProblem cspatrs;
    private final Map<FunctionSymbol, FunctionSymbol> def_tup;

    private final int hashCode;

    /**
     * Creates a CSPADP Problem.
     */
    private CSPADPProblem(ImmutableSet<PARule> P, CSPATRSProblem cspatrs, Map<FunctionSymbol, FunctionSymbol> def_tup) {
        super("CSPADP", "CSPADP");
        this.P = P;
        this.cspatrs = cspatrs;
        this.def_tup = def_tup;
        if (this.P != null && this.cspatrs != null) {
            this.hashCode = P.hashCode()*8831123 + cspatrs.hashCode() * 1293527;
        } else {
            this.hashCode = 0;
        }
    }

    /**
     * Creates a CSPADP Problem.
     */
    public static CSPADPProblem create(ImmutableSet<PARule> P, CSPATRSProblem cspatrs, Map<FunctionSymbol, FunctionSymbol> def_tup) {
        return new CSPADPProblem(P, cspatrs, def_tup);
    }

    /**
     * Returns the signature of P, R, S, E.
     */
    public synchronized ImmutableSet<FunctionSymbol> getSignature() {
        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.P);
        signature.addAll(this.cspatrs.getSignature());
        return ImmutableCreator.create(signature);
    }

    /**
     * Returns the signature of P, R, S, E without tuple symbols.
     */
    public synchronized ImmutableSet<FunctionSymbol> getSignatureNoTuple() {
        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.P);
        signature.addAll(this.cspatrs.getSignature());
        signature.removeAll(this.getTupleSymbols());
        return ImmutableCreator.create(signature);
    }

    /**
     * Returns the signature of S and E.
     */
    public synchronized ImmutableSet<FunctionSymbol> getSignatureSE() {
        return this.cspatrs.getSignatureSE();
    }

    /**
     * Returns the tuple symbols of P.
     */
    public synchronized ImmutableSet<FunctionSymbol> getTupleSymbols() {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        for (PARule dp : this.P) {
            res.add(dp.getLeft().getRootSymbol());
            res.add(((TRSFunctionApplication) dp.getRight()).getRootSymbol());
        }
        return ImmutableCreator.create(res);
    }

    public ImmutableSet<PARule> getP() {
        return this.P;
    }

    public CSPATRSProblem getCSPATRS() {
        return this.cspatrs;
    }

    public Map<FunctionSymbol, FunctionSymbol> getDefTup() {
        return this.def_tup;
    }

    public ImmutableSet<PARule> getR() {
        return this.cspatrs.getR();
    }

    public ImmutableSet<Rule> getS() {
        return this.cspatrs.getS();
    }

    public ImmutableSet<Equation> getE() {
        return this.cspatrs.getE();
    }

    public ImmutableMap<String, ImmutableList<String>> getSortMap() {
        return this.cspatrs.getSortMap();
    }

    public ImmutableMap<String, ImmutableSet<Integer>> getMu() {
        return this.cspatrs.getMu();
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
        CSPADPProblem other = (CSPADPProblem) oth;
        return this.P.equals(other.P) && this.cspatrs.equals(other.cspatrs);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public String export(Export_Util o) {
        StringBuffer s = new StringBuffer();
        s.append(o.export("Context-sensitive PA-based DP problem:"));
        s.append(o.cond_linebreak());
        s.append(o.export("The replacement map mu contains the following entries:"));
        s.append(o.cond_linebreak());
        Set<String> tmp = new LinkedHashSet<String>();
        for (Map.Entry<String, ? extends Set<Integer>> repEntry : this.getMu().entrySet()) {
            Set<Integer> repl = repEntry.getValue();
            ArrayList<Integer> shiftSet = new ArrayList<Integer>(repl.size());
            for (Integer i : repl) {
                shiftSet.add(i + 1);
            }
            tmp.add(repEntry.getKey() + ": " + o.set(shiftSet, Export_Util.SIMPLESET));
        }
        s.append(o.set(tmp, Export_Util.RULES));
        s.append(o.linebreak());
        if (this.P.isEmpty()) {
            s.append("P is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("P consists of the following dependency pairs:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.P, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        if (this.getR().isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getR(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        if (this.getS().isEmpty()) {
            s.append("S is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("S consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getS(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        if (this.getE().isEmpty()) {
            s.append("E is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("E consists of the following equations:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getE(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        s.append(o.export("We have to consider all minimal (P, R, S, E, mu)-chains."));

        return s.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        throw new UnsupportedOperationException();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        // TODO Auto-generated method stub
        return null;
    }
}
