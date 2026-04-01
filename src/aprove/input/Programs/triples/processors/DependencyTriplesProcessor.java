package aprove.input.Programs.triples.processors;

import java.util.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.input.Programs.triples.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;


public class DependencyTriplesProcessor implements Processor {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        PrologProblem ppbl = (PrologProblem) obl;
        return this.isLogicProgram(ppbl.getProgram());
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
        Abortion aborter, RuntimeInformation rti) throws AbortionException {
        PrologProblem ppbl = (PrologProblem) obl;
        PrologProgram program = ppbl.getProgram();
        List<PrologClause> clauses = program.getClauses();

        List<PrologClause> newClauses = new ArrayList<PrologClause>();

        for (PrologClause clause : clauses) {
            PrologTerm h = clause.getHead();
            PrologTerm b = clause.getBody();
            PrologTerm nb = b;
            while (nb != null) {
                PrologClause nc = new PrologClause(h,nb) ;
                newClauses.add(nc);

                nb = this.deleteLast(nb);

            }
        }
        PrologProgram triples = new PrologProgram();
        for (PrologClause newClause : newClauses) {
            triples.addClause(newClause);
        }
        //System.err.println(newClauses);

        Set<TriplesProblem> newProblems = new LinkedHashSet<TriplesProblem>();
        List<Afs> afss = ppbl.createListOfAfs("");
        for (Afs afs : afss){
            TriplesProblem newProblem = new TriplesProblem(triples,program,afs);
            newProblems.add(newProblem);
        }
        return ResultFactory.provedAnd(
            newProblems,
            YNMImplication.EQUIVALENT,
            new DependencyTriplesProof()
        );
    }



    public static class DependencyTriplesProof extends Proof.DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "TODO";
        }

    }
    /**
     *
     * @param b
     * @return
     * Checks if PrologTerm b is a conjunction
     */
    private PrologTerm deleteLast(PrologTerm b) {
        if (b.isConjunction()) {
            if (!b.getArgument(1).isConjunction()){
                return b.getArgument(0);
            }
            List<PrologTerm> args = new ArrayList<PrologTerm>();
            args.add(b.getArgument(0));
            args.add(this.deleteLast(b.getArgument(1)));
            PrologTerm t = new PrologTerm(PrologBuiltin.CONJUNCTION_NAME, args);
            return t;
        } else {
            return null;
        }
    }

    /**
     * Tests whether or not the given PrologProgram is a logic program.
     * @param prologProg The PrologProgram to test.
     * @return True, if it is a logic program. False otherwise.
     */
    private boolean isLogicProgram(PrologProgram prologProg) {
        Set<FunctionSymbol> preds = prologProg.createSetOfAllPredicates();
        for (PrologClause clause : prologProg.getClauses()) {
            if (!clause.isLogicProgramCompatible(preds)) {
                return false;
            }
        }
        return prologProg.createSetOfDefinedPredicates().equals(
            prologProg.createSetOfAllPredicates()
        );
    }

}
