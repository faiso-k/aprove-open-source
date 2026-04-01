package aprove.input.Programs.triples.processors;

import java.util.*;

import aprove.input.Programs.prolog.structure.*;
import aprove.input.Programs.triples.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class DependencyGraphProcessor extends TriplesProblemProcessor {

    @Override
    public boolean isTriplesApplicable(TriplesProblem pp) {
        return true;
    }

    @Override
    public Result processTriplesProblem(TriplesProblem tp, Abortion aborter)
            throws AbortionException {
        // extract dependency triples from problem
        // build graph by putting each dependency triple as a node
        // put an edge from a node A to a node B whenever the last atom
        // in the body of A unifies with the first atom in the body of B
        Graph<PrologClause,Object> graph = new Graph<PrologClause,Object>();
        PrologProgram triples = tp.getTriples();
        for (PrologClause theOne : triples.getClauses()) {
            graph.addNode(new Node<PrologClause>(theOne));
        }
        for (PrologClause theOne : triples.getClauses()) {
            for (PrologClause theOther : triples.getClauses()) {
                PrologTerm lastAtom = theOne.getBody();
                while (lastAtom.isConjunction()) {
                    lastAtom = lastAtom.getArgument(1);
                }
                //System.err.println(lastAtom);
                PrologTerm firstAtom = theOther.getHead();
                FreshNameGenerator fridge =
                    new FreshNameGenerator(
                        firstAtom.createSetOfAllVariables(),
                        FreshNameGenerator.PROLOG_VARS
                    );
                PrologTerm lastCopy =
                    lastAtom.applySubstitution(
                        lastAtom.computeNonAbstractVarNameRefreshment(fridge)
                    );
                if (lastCopy.unifiesWith(firstAtom)) {
                    Node<PrologClause> theOneNode =
                        graph.getNodeFromObject(theOne);
                    Node<PrologClause> theOtherNode =
                        graph.getNodeFromObject(theOther);
                    graph.addEdge(theOneNode, theOtherNode);
                }
            }
        }
        //System.err.println(graph);
        Set<TriplesProblem> newProblems = new LinkedHashSet<TriplesProblem>();
        Set<Cycle<PrologClause>> components = graph.getSCCs();
        for (Cycle<PrologClause> component : components) {
            // for each component, build a new TriplesProblem like tp but
            // with only the dependency triples from that component
            System.err.println(component);

            List<PrologClause> newClauses = new ArrayList<PrologClause>();

            for (Node<PrologClause> node : component){
                newClauses.add(node.getObject());
            }

            PrologProgram newTriples = new PrologProgram();
            for (PrologClause newClause : newClauses) {
                newTriples.addClause(newClause);
            }
            //System.err.println(newTriples);

            TriplesProblem newProblem =
                new TriplesProblem(newTriples,tp.getClauses(),tp.getAfs());

            newProblems.add(newProblem);
        }
        if (
                newProblems.size() == 1 &&
                newProblems.iterator().next().getTriples().getClauses().equals(
                    triples.getClauses()
                )
        ) {
            //System.err.println("\n\n\n\n");
            //System.err.println(triples);
            return ResultFactory.unsuccessful();
        }
        return ResultFactory.provedAnd(
            newProblems,
            YNMImplication.EQUIVALENT,
            new DependencyGraphProof()
        );
    }

    public static class DependencyGraphProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "TODO";
        }

    }

}
