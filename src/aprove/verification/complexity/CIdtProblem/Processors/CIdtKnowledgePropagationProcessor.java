package aprove.verification.complexity.CIdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CIdtProblem.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class CIdtKnowledgePropagationProcessor extends CIdtProcessor<Result> {

    public CIdtKnowledgePropagationProcessor() {
        super("CIdtKnowledgeGeneration");
    }

    @Override
    public boolean isCompatible(Mark<?> mark) {
        return false;
    }

    @Override
    protected Result processCIdtProblem(CIdtProblem idt, Abortion aborter) throws AbortionException {

        IDependencyGraph graph = idt.getIdpGraph();
        CIdtProblem newCIdt = idt;
        boolean successful = true;

        Set<IEdge> removedFromS = new LinkedHashSet<>();
        Set<IEdge> addedToK = new LinkedHashSet<>();

        while (successful) {
            successful = false;

            Set<IEdge> newS = new LinkedHashSet<>(newCIdt.getS());
            Set<IEdge> newK = new LinkedHashSet<>(newCIdt.getK());

            for (INode node : graph.getNodes()) {
                aborter.checkAbortion();

                boolean allPreEdgesInK = true;
                for (Set<IEdge> edges : graph.getPredecessors(node).values()) {
                    for (IEdge e : edges) {
                        if (e.type.isInf()) {
                            if (!newK.contains(e)) {
                                allPreEdgesInK = false;
                                break;
                            }
                        }
                    }

                }
                if (allPreEdgesInK) {
                    for (Set<IEdge> edges : graph.getSuccessors(node).values()) {
                        for (IEdge e : edges) {
                            if (e.type.isInf()) {
                                if (newS.remove(e)) {
                                    successful = true;
                                    if (idt.getS().contains(e)) {
                                        removedFromS.add(e);
                                    }
                                }

                                if (newK.add(e)) {
                                    if (!idt.getK().contains(e)) {
                                        addedToK.add(e);
                                    }
                                    successful = true;
                                }
                            }
                        }
                    }
                }
            }

            if (successful) {
                newCIdt = newCIdt.change(graph, ImmutableCreator.create(newS), ImmutableCreator.create(newK));
            }
        }

        if (idt != newCIdt) {
            return ResultFactory.proved(newCIdt, BothBounds.create(), new CIdtKnowledgePropagationProof(removedFromS, addedToK));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    @Override
    protected boolean isCIdtApplicable(CIdtProblem idt) {
        return true;
    }

    public class CIdtKnowledgePropagationProof extends DefaultProof {

        private final Collection<IEdge> removedFromS;
        private final Collection<IEdge> addedToK;

        public CIdtKnowledgePropagationProof(Collection<IEdge> removedFromS, Collection<IEdge> addedToK) {
            this.removedFromS = removedFromS;
            this.addedToK = addedToK;
        }

        @Override
        public String export(Export_Util eu, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("The following edges were removed from S:");
            sb.append(eu.linebreak());
            sb.append(eu.set(this.removedFromS, Export_Util.NICE_SET));

            sb.append(eu.linebreak());
            sb.append(eu.linebreak());

            sb.append("The following edges were added to K:");
            sb.append(eu.linebreak());
            sb.append(eu.set(this.addedToK, Export_Util.NICE_SET));

            return sb.toString();
        }

    }

}
