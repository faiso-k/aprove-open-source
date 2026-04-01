package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CdtProblem.Utils.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Split each node of the Cdt graph which is not part of an SCC, i.e.,
 * for each argument of the compound symbol introduce a new node with
 * the lhs of the original Cdt and a unary right hand side.
 */
public class CdtGraphSplitRhsProcessor extends CdtProblemProcessor{

    @Override
    protected boolean isCdtApplicable(CdtProblem obl) {
        return !Options.certifier.isCpf();
    }

    @Override
    protected Result processCdt(CdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        Set<Cdt> sccNodes = this.getNodesInSccs(cdtProblem);
        FreshNameGenerator fng = new FreshNameGenerator(
                cdtProblem.getSignature(), FreshNameGenerator.APPEND_NUMBERS);
        FunctionSymbol compound = FunctionSymbol.create(
                fng.getFreshName("c", false), 1);

        Map<Node<Cdt>, Set<Cdt>> transformations = new LinkedHashMap<Node<Cdt>, Set<Cdt>>();
        for (Node<Cdt> node : cdtProblem.getGraph().getGraph().getNodes()) {
            Cdt cdt = node.getObject();
            if (!sccNodes.contains(cdt) && cdt.getRuleRHSArgs().size() > 1) {
                transformations.put(node, this.split(compound, cdt));
            }

        }

        if (transformations.isEmpty()) {
            return ResultFactory.unsuccessful("Could not split any RHS");
        } else {
            CdtProblem newCdtProblem =
                cdtProblem.createTransformedComplete(null, transformations);
            return ResultFactory.proved(newCdtProblem,
                    BothBounds.create(), new CdtGraphSplitRhsProof());
        }
    }

    /**
     * Splits a tuple in one tuple for each RHS argument
     * @param cdt
     * @return
     */
    private Set<Cdt> split(FunctionSymbol compound, Cdt cdt) {
        List<TRSFunctionApplication> rhsArgs = cdt.getRuleRHSArgs();
        if (rhsArgs.size() <= 1) {
            return java.util.Collections.singleton(cdt);
        }

        Set<Cdt> result = new LinkedHashSet<Cdt>();

        for (TRSFunctionApplication rhsArg : rhsArgs) {
            Rule depTuple = Rule.create(
                    cdt.getRuleLHS(),
                    TRSTerm.createFunctionApplication(compound, rhsArg)
                    );
            result.add(Cdt.create(depTuple));
        }
        return result;
    }

    /**
     * Computes the set of tuples contained in any SCC in the graph
     */
    private Set<Cdt> getNodesInSccs(CdtProblem cdtProblem) {
        BasicCdtGraph cdg = cdtProblem.getGraph();
        Graph<Cdt, BitSet> g = cdg.getCopyOfGraph();
        LinkedHashSet<Cycle<Cdt>> sccs = g.getSCCs(true);
        LinkedHashSet<Cdt> sccNodes = new LinkedHashSet<Cdt>();
        for (Cycle<Cdt> scc : sccs) {
            sccNodes.addAll(scc.getNodeObjects());
        }
        return sccNodes;
    }

    public class CdtGraphSplitRhsProof extends CpxProof {

        public CdtGraphSplitRhsProof() {
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME Real proof!
            return "Split RHS of tuples not part of any SCC";
        }

    }
}
