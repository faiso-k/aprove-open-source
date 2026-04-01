package aprove.verification.relative.RelADPProblem;

import java.util.*;
import java.util.stream.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Relative ADP Problem as described in [IJCAR24].
 * 
 * @author Grigory Vartanyan, Jan-Christoph Kassing
 * @version $Id$
 */
public class RelADPProblem extends DefaultBasicObligation implements Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    private final Set<Rule> P_abs;
    private final Set<Rule> P_rel;
    private final QTRSProblem sWithQ;

    private final RelDepGraph rel_dep_graph;
    private volatile ImmutableSet<FunctionSymbol> signature;

    private final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    // Make problem from P_abs, P_rel and cached graph
    public RelADPProblem(
        Set<Rule> p_abs,
        Set<Rule> p_rel,
        QTRSProblem withQ,
        RelDepGraph graph,
        BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap
    ) {
        super("RelADPP", "Relative Annotated Dependency Pair Problem");
    
        this.P_abs = p_abs;
        this.P_rel = p_rel;
        this.sWithQ = withQ;
        this.rel_dep_graph = graph;
        this.annoMap = annoMap;

        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(P_abs);
        signature.addAll(CollectionUtils.getFunctionSymbols(P_rel));
        signature.addAll(CollectionUtils.getFunctionSymbols(sWithQ.getR()));
        this.signature = ImmutableCreator.create(signature);
    }

    public RelADPProblem(
        Set<Rule> p_abs,
        Set<Rule> p_rel,
        QTRSProblem withQ,
        BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap
    ) {
        this(p_abs, p_rel, withQ, RelDepGraph.create(p_abs, p_rel, withQ, null, annoMap), annoMap);
    }

    public RelADPProblem(
        RelDepGraph graph,
        QTRSProblem withQ,
        BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap
    ) {
        this(graph.getPAbs(), graph.getPRel(), withQ, graph, annoMap);
    }

    public static RelADPProblem create(
        Set<Rule> p_abs,
        Set<Rule> p_rel,
        QTRSProblem sWithQ,
        BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap
    ) {
        return new RelADPProblem(p_abs, p_rel, sWithQ, annoMap);
    }

    public RelADPProblem getSubProblem(final RelDepGraph graph) {
        if (Globals.useAssertions) {
            assert (this.rel_dep_graph.getGraph().getNodes().containsAll(graph.getGraph().getNodes()));  // TODO: this will fail if unmarked
            assert (this.rel_dep_graph.getGraph().getEdges().containsAll(graph.getGraph().getEdges()));
        }

        return new RelADPProblem(graph, this.sWithQ, this.annoMap);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    public Set<Rule> getPAbs() {
        return P_abs;
    }

    public Set<Rule> getPRel() {
        return P_rel;
    }

    public QTRSProblem getQ() {
        return sWithQ;
    }

    public ImmutableSet<Rule> getR() {
        return sWithQ.getR();
    }

    public RelDepGraph getRelDepGraph() {
        return rel_dep_graph;
    }

    public Set<FunctionSymbol> getSignature() {
        return signature;
    }

    public Set<FunctionSymbol> getAnnotatedSignature() {
        return annoMap.getRLMap().keySet();
    }

    public Set<FunctionSymbol> getFullSignature() {
        Set<FunctionSymbol> res = new HashSet<>();
        res.addAll(signature);
        res.addAll(annoMap.getRLMap().keySet());
        return res;
    }

    public BidirectionalMap<FunctionSymbol, FunctionSymbol> getBiAnnoMap() {
        return annoMap;
    }

    public Map<FunctionSymbol, FunctionSymbol> getAnnotator() {
        return annoMap.getLRMap();
    }

    public Map<FunctionSymbol, FunctionSymbol> getDeannotator() {
        return annoMap.getRLMap();
    }
    
    public int countAnnoInRHS() {
        int res = 0;
        for (Rule rule: P_abs) {
            res += rule.countAnnos(annoMap.getRLMap());
        }
        for (Rule rule: P_rel) {
            res += rule.countAnnos(annoMap.getRLMap());
        }
        return res;
    }

    /** 
     * @return true, if this RDPProblem is non-relative, ie P_rel is empty
     * */
    public boolean isNonRelative() {
        for (Rule rule: P_rel) {
            TRSTerm rhs = rule.getRight();
            for (FunctionSymbol fs: rhs.getFunctionSymbols()) {
                if (this.annoMap.getRLMap().containsKey(fs)) {
                    return false;
                }
            }
        }

        return true;
    }

    public boolean isMarked(Rule rule) {
        return P_rel.contains(rule);
    }
    
    // ================================================================================
    // Utility
    // ================================================================================

    @Override
    public String getStrategyName() {
        return "relqadp";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        // TODO what is this
        return null;
    }

    @Override
    public String export(Export_Util eu) {
        final StringBuilder s = new StringBuilder();
        s.append(eu.export("Relative ADP Problem with"));
        s.append(eu.cond_linebreak());

        if (P_abs.isEmpty()) {
            s.append("No absolute ADPs, ");
        } else {
            s.append(eu.export("absolute ADPs:"));
            s.append(eu.cond_linebreak());
            s.append(eu.set(P_abs, Export_Util.RULES));
            s.append(eu.cond_linebreak());
        }

        if (P_rel.isEmpty()) {
            s.append("and no relative ADPs.");
        } else {
            s.append(eu.export("and relative ADPs:"));
            s.append(eu.cond_linebreak());
            s.append(eu.set(P_rel, Export_Util.RULES));
            s.append(eu.cond_linebreak());
        }

        return s.toString();
    }
}
