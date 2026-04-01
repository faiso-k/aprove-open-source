package aprove.verification.relative.RDTProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * @author Grigory Vartanyan
 * @version $Id$
 */
public class RDTProblem extends DefaultBasicObligation implements Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    private final Set<CoupledPosDepTuple> D1;
    private final Set<CoupledPosDepTuple> D2;
    private final QTRSProblem sWithQ;

    private final RelDepGraph graph;
    private volatile ImmutableSet<FunctionSymbol> signature;

//    private final RelDependencyGraph graph;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    // Make problem from Di, R and graph
    public RDTProblem(
        Set<CoupledPosDepTuple> d1,
        Set<CoupledPosDepTuple> d2,
        QTRSProblem withQ,
        RelDepGraph graph
    ) {
        super("RDTP", "Relative Dependency Tuple Problem");
    
        D1 = d1;
        D2 = d2;
        this.sWithQ = withQ;
        this.graph = graph;

        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.D1);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.D2));
        signature.addAll(CollectionUtils.getFunctionSymbols(this.sWithQ.getR()));
        this.signature = ImmutableCreator.create(signature);
    }

    // Make problem from Di and R. Construct graph.
    public RDTProblem(
        Set<CoupledPosDepTuple> d1,
        Set<CoupledPosDepTuple> d2,
        QTRSProblem r
    ) {
        super("RDTP", "Relative Dependency Tuple Problem");

        D1 = d1;
        D2 = d2;
        sWithQ = r;
        graph = RelDepGraph.create(d1, d2, r);

        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.D1);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.D2));
        signature.addAll(CollectionUtils.getFunctionSymbols(this.sWithQ.getR()));
        this.signature = ImmutableCreator.create(signature);
    }

    public RDTProblem(RelDepGraph graph, QTRSProblem withQ) {
        super("RDTP", "Relative Dependency Tuple Problem");

        this.sWithQ = withQ;
        this.graph = graph;
        D1 = graph.getD1();
        D2 = graph.getD2();

        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.D1);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.D2));
        signature.addAll(CollectionUtils.getFunctionSymbols(this.sWithQ.getR()));
        this.signature = ImmutableCreator.create(signature);
    }

    public static RDTProblem create(
        Set<CoupledPosDepTuple> d1,
        Set<CoupledPosDepTuple> d2,
        QTRSProblem sWithQ
    ) {
        return new RDTProblem(d1, d2, sWithQ);
    }

    public RDTProblem getSubProblem(final RelDepGraph graph) {
        if (Globals.useAssertions) {
            assert (this.graph.getGraph().getNodes().containsAll(graph.getGraph().getNodes()));  // TODO: this will fail if unmarked
            assert (this.graph.getGraph().getEdges().containsAll(graph.getGraph().getEdges()));
        }

        return new RDTProblem(graph, this.sWithQ);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    public Set<CoupledPosDepTuple> getD1() {
        return D1;
    }

    public Set<CoupledPosDepTuple> getD2() {
        return D2;
    }

    public QTRSProblem getQ() {
        return sWithQ;
    }

    public ImmutableSet<Rule> getR() {
        return sWithQ.getR();
    }

    public RelDepGraph getDependencyGraph() {
        return graph;
    }

    public Set<FunctionSymbol> getSignature() {
        return signature;
    }

    /** 
     * @return true, if this RDPProblem is non-relative, ie D2 is empty
     * */
    public boolean isNonRelative() {
        return D2.isEmpty();
    }

    public boolean isMarked(CoupledPosDepTuple rule) {
        return D2.contains(rule);
    }
    
    // ================================================================================
    // Utility
    // ================================================================================

    @Override
    public String getStrategyName() {
        return "relqdt";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        // TODO what is this
        return null;
    }

    @Override
    public String export(Export_Util eu) {
        final StringBuilder s = new StringBuilder();
        s.append(eu.export("Relative DT Problem with"));
        s.append(eu.cond_linebreak());

        if (this.getD1().isEmpty()) {
            s.append("No absolute tuples, ");
//            s.append(eu.linebreak());
        } else {
            s.append(eu.export("absolute tuples:"));
            s.append(eu.cond_linebreak());
            s.append(eu.set(this.getD1(), Export_Util.RULES));
            s.append(eu.cond_linebreak());
        }

        if (this.getD2().isEmpty()) {
            s.append("no relative tuples ");
//            s.append(eu.linebreak());
        } else {
            s.append(eu.export("relative tuples:"));
            s.append(eu.cond_linebreak());
            s.append(eu.set(this.getD2(), Export_Util.RULES));
            s.append(eu.cond_linebreak());
        }

        if (this.getR().isEmpty()) {
            s.append("and no rules.");
//            s.append(eu.linebreak());
        } else {
            s.append(eu.export("and rules:"));
            s.append(eu.cond_linebreak());
            s.append(eu.set(this.getR(), Export_Util.RULES));
            s.append(eu.cond_linebreak());
        }

        return s.toString();
    }
}
