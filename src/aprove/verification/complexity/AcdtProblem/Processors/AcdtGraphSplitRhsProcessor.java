package aprove.verification.complexity.AcdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.AcdtProblem.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Split each node of the Cdt graph which is not part of an SCC, i.e.
 * for each argument of the compound symbol introduce a new node with
 * the lhs and an unary compound symbol (and the argument).
 * replace it by new nodes which the same LHS end exactly
 * remove all tuple-subterms of the
 * RHS which do not have an outgoing edge (i.e. none of the edges
 * of the node "belongs" to the tuple-subterm).
 */
public class AcdtGraphSplitRhsProcessor extends AcdtProblemProcessor{

    @Override
    protected boolean isCdtApplicable(AcdtProblem obl) {
        return true;
    }

    @Override
    protected Result processCdt(AcdtProblem cdtProblem, Abortion aborter)
            throws AbortionException {
        Set<Acdt> sccNodes = this.getNodesInSccs(cdtProblem);
        FreshNameGenerator fng = new FreshNameGenerator(
                cdtProblem.getSignature(), FreshNameGenerator.APPEND_NUMBERS);
        FunctionSymbol compound = FunctionSymbol.create(
                fng.getFreshName("c", false), 1);

        Map<Node<Acdt>, Set<Acdt>> transformations = new LinkedHashMap<Node<Acdt>, Set<Acdt>>();
        for (Node<Acdt> node : cdtProblem.getGraph().getGraph().getNodes()) {
            Acdt cdt = node.getObject();
            if (!sccNodes.contains(cdt) && cdt.getRuleRHSArgs().size() != 1) {
                transformations.put(node, this.split(compound, cdt));
            }

        }

        if (transformations.isEmpty()) {
            return ResultFactory.unsuccessful("Could not split any RHS");
        } else {
            AcdtProblem newCdtProblem = cdtProblem.createTransformed(transformations);
            return ResultFactory.proved(newCdtProblem,
                    BothBounds.create(), new CdtGraphSplitRhsProof());
        }
    }

    /**
     * Splits a tuple in one tuple for each RHS argument
     * @param cdt
     * @return
     */
    private Set<Acdt> split(FunctionSymbol compound, Acdt cdt) {
        ArrayList<TRSFunctionApplication> rhsArgs = cdt.getRuleRHSArgs();
        final int n = rhsArgs.size();
        if (n == 0) {
            return java.util.Collections.emptySet();
        } else if (n == 1) {
            return java.util.Collections.singleton(cdt);
        }

        Set<Acdt> result = new LinkedHashSet<Acdt>();
        TupleDefinedPositions tdps = cdt.getTupleDefPos();

        int i=0;
        for (TRSFunctionApplication rhsArg : rhsArgs) {
            BitSet bs = new BitSet();
            bs.set(0, n);
            bs.clear(i);
            Rule depTuple = Rule.create(
                    cdt.getRuleLHS(),
                    TRSTerm.createFunctionApplication(compound, rhsArg)
                    );
            result.add(Acdt.create(depTuple, cdt.getBaseRule(), tdps.filter(bs)));
            i++;
        }
        return result;
    }

    /**
     * Computes the set of tuples contained in any SCC in the graph
     */
    private Set<Acdt> getNodesInSccs(AcdtProblem cdtProblem) {
        BasicAcdtGraph cdg = cdtProblem.getGraph();
        Graph<Acdt, BitSet> g = cdg.getCopyOfGraph();
        LinkedHashSet<Cycle<Acdt>> sccs = g.getSCCs(true);
        LinkedHashSet<Acdt> sccNodes = new LinkedHashSet<Acdt>();
        for (Cycle<Acdt> scc : sccs) {
            sccNodes.addAll(scc.getNodeObjects());
        }
        return sccNodes;
    }

    public class CdtGraphSplitRhsProof extends DefaultProof {

        public CdtGraphSplitRhsProof() {
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            // FIXME Real proof!
            return "Split RHS of tuples not part of any SCC";
        }

    }
}
