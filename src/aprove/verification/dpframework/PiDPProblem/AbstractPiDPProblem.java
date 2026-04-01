package aprove.verification.dpframework.PiDPProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public abstract class AbstractPiDPProblem extends DefaultBasicObligation
        implements Immutable, HTML_Able, HasTRSTerms, DOT_Able {
    /*
     * real values
     */
    private final ImmutableSet<GeneralizedRule> P;
    private final AbstractPiTRSProblem rWithPi;

    /*
     * computes / cached values
     */
    private final PiDependencyGraph graph;
    private final int hashCode;
    private volatile ImmutableSet<GeneralizedRule> usableRules;
    private volatile ImmutableSet<FunctionSymbol> signature;

    protected AbstractPiDPProblem(String shortName, String longName,
            ImmutableSet<GeneralizedRule> P, AbstractPiTRSProblem rWithPi,
            PiDependencyGraph graph) {
        super(shortName, longName);
        if (Globals.useAssertions) {
            assert (P != null && rWithPi != null); // perhaps also check whether the graph is valid
        }
        this.P = P;
        this.rWithPi = rWithPi;
        this.graph = graph;
        this.signature = null;
        this.hashCode = 8831123 * P.hashCode() + 1293527 * rWithPi.hashCode();
    }

    /*- accessors ------------------------------------------------------------*/

    /**
     * returns a subproblem with smaller P
     */
    public Set<? extends AbstractPiDPProblem> getSubProblems(ImmutableSet<GeneralizedRule> P) {
        return this.getSubProblems(P, this.graph.getSubGraphFromPRules(P));
    }

    /**
     * returns a subproblem with smaller graph
     * @param graph
     * @return
     */
    public Set<? extends AbstractPiDPProblem> getSubProblems(PiDependencyGraph graph) {
        return this.getSubProblems(graph.getP(), graph);
    }

    public PiDependencyGraph getDependencyGraph() {
        return this.graph;
    }

    /**
     * returns the set of all terms in P,Q,R. the resulting set may be safely
     * modified.
     */
    @Override
    public Set<TRSTerm> getTerms() {
        Set<TRSTerm> terms = CollectionUtils.getTerms(this.P);
        terms.addAll(CollectionUtils.getTerms(this.rWithPi.getR()));
        return terms;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        if (this.signature == null) {
            this.computeSignatures();
        }
        return this.signature;
    }

    public ImmutableSet<GeneralizedRule> getUsableRules() {
        if (this.usableRules == null) {
            // only synchronize if cache is not yet computed,
            // synchronize to omit multiple computation of usable rules
            synchronized (this) {
                if (this.usableRules == null) {
                    this.usableRules = PiUsableRules.computeUsableRules(this);
                }
            }
        }
        return this.usableRules;
    }

    public ImmutableSet<GeneralizedRule> getP() {
        return this.P;
    }

    public ImmutableSet<GeneralizedRule> getR() {
        return this.rWithPi.getR();
    }

    public ImmutableAfs getPi() {
        return this.rWithPi.getPi();
    }

    public AbstractPiTRSProblem getRwithPi() {
        return this.rWithPi;
    }

    /*- abstract methods -----------------------------------------------------*/

    abstract protected AbstractPiDPProblem createProblem(ImmutableSet<GeneralizedRule> P,
        AbstractPiTRSProblem rWithPi,
        PiDependencyGraph graph);

    /**
     * returns subproblems with smaller P, the graph and P must have the same
     * nodes
     * @param P
     * @param graph
     * @return list of subproblems
     */
    abstract protected Set<? extends AbstractPiDPProblem> getSubProblems(ImmutableSet<GeneralizedRule> P,
        PiDependencyGraph graph);

    abstract public AbstractPiDPProblem getSameProblem(ImmutableAfs Pi);

    abstract public AbstractPiDPProblem getSubProblemWithSmallerR(ImmutableSet<GeneralizedRule> R);

    @Override
    abstract public String export(Export_Util o);

    /*- export ---------------------------------------------------------------*/

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String toDOT() {
        return this.getDependencyGraph().toDOT();
    }

    /*- Object methods -------------------------------------------------------*/

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

        AbstractPiDPProblem other = (AbstractPiDPProblem) oth;
        if (!this.rWithPi.equals(other.rWithPi)) {
            return false;
        }

        return this.P.equals(other.P);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    /*- private methods ------------------------------------------------------*/

    private void computeSignatures() {
        synchronized (this) {
            Set<FunctionSymbol> signature =
                CollectionUtils.getFunctionSymbols(this.P);
            signature.addAll(CollectionUtils.getFunctionSymbols(this.rWithPi.getR()));
            this.signature = ImmutableCreator.create(signature);
        }
    }
}
