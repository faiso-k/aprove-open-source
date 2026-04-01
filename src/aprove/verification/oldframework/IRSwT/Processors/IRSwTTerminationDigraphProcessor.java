package aprove.verification.oldframework.IRSwT.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IRSwT.Digraph.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Computes the missing parts of the termination digraph and returns its
 * SCCs or a problem that is annotated with the fully evaluated digraph.
 * @author Matthias Hoelzel
 *
 */
public class IRSwTTerminationDigraphProcessor extends Processor.ProcessorSkeleton {
    /**
     * Constructor!
     */
    public IRSwTTerminationDigraphProcessor() {
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && !((IRSwTProblem) obl).isBounded();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        // 1. Get ready:
        assert obl instanceof IRSwTProblem : "Wrong obligation!";
        final IRSwTProblem irswt = (IRSwTProblem) obl;
        final FreshNameGenerator fng = irswt.createFreshNameGenerator();
        final PartiallyComputedDigraph<IGeneralizedRule> originalDigraph = irswt.getTerminationDigraph();
        PartiallyComputedDigraph<IGeneralizedRule> digraph;
        if (originalDigraph == null) {
            // Until now there is no such graph, so we create a new one:
            digraph = new PartiallyComputedDigraph<>(irswt.getRules());
        } else {
            // Make a copy, because the digraph of the problem is frozen (immutable).
            digraph = new PartiallyComputedDigraph<>(originalDigraph);
        }

        // 2. Compute digraph:
        final TerminationDigraphComputation tdc =
            new TerminationDigraphComputation(digraph, new FullSharingFactory<SMTLIBTheoryAtom>(), fng, aborter);
        digraph = tdc.computeDigraph();

        // 3. Split it into SCCs:
        final LinkedList<IRSwTProblem> newProblems = new LinkedList<>();
        for (final Set<IGeneralizedRule> scc : digraph.getSCCs()) {
            final PartiallyComputedDigraph<IGeneralizedRule> sccDigraph = digraph.getInducedSubgraph(scc);
            if (!sccDigraph.hasEdges()) {
                continue;
            }
            newProblems.add(new IRSwTProblem(ImmutableCreator.create(scc), sccDigraph));
        }

        if (originalDigraph != null
            && originalDigraph.isFullyEvaluated()
            && newProblems.size() == 1
            && newProblems.getFirst().getRules().containsAll(irswt.getRules()))
        {
            return ResultFactory.unsuccessful();
        }

        return ResultFactory.provedAnd(
            newProblems,
            YNMImplication.EQUIVALENT,
            new IRSwTTerminationDigraphProof(digraph, newProblems));
    }

    /**
     * A truly outrageous proof!
     * @author Matthias Hoelzel
     */
    class IRSwTTerminationDigraphProof extends DefaultProof {
        /** The computed graph */
        private final PartiallyComputedDigraph<IGeneralizedRule> digraph;
        private final List<IRSwTProblem> newProblems;

        /**
         * Constructor!
         * @param terminatonDigraph computed graph
         */
        public IRSwTTerminationDigraphProof(final PartiallyComputedDigraph<IGeneralizedRule> terminatonDigraph, List<IRSwTProblem> newProblems) {
            this.digraph = terminatonDigraph;
            this.newProblems = newProblems;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {

            return eu.tttext("Constructed termination digraph!") + eu.linebreak() + this.digraph.export(eu);
        }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            Element sccs = CPFTag.LTS_SCC_DECOMP.create(doc);
            Iterator<IRSwTProblem> ltsIter = this.newProblems.iterator();
            for (Element proof : childrenProofs) {
                IRSwTProblem scc = ltsIter.next();
                Element locations = CPFTag.LTS_SCC.create(doc);
                Set<FunctionSymbol> fs = new HashSet<>();
                for (IGeneralizedRule rule : scc.getRules()) {
                    fs.add(rule.getRootSymbol());
                }
                for (FunctionSymbol f : fs) {
                    locations.appendChild(CPFTag.LTS_LOCATION_DUP.create(doc, f.getName()));
                }
                sccs.appendChild(CPFTag.LTS_SCC_PROOF.create(doc, locations, proof));
            }
            return sccs;
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
        }

    }
}
