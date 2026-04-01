package aprove.input.Programs.triples.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.structure.*;
import aprove.input.Programs.triples.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author cryingshadow
 * @version $Id$
 */
public class UndefinedPredicateInTriplesTransformer
extends TriplesProblemProcessor {


    protected final static Logger logger =
        Logger.getLogger(
            "aprove.input.Programs.triples.processors.UndefinedPredicateInTriplesTransformer"
        );


    /**
     * Tests whether or not the given PrologProgram is a logic program.
     * @param prologProg The PrologProgram to test.
     * @return True, if it is a logic program. False otherwise.
     */
    private boolean isLogicProgramCompatible(PrologProgram prologProg) {
        Set<FunctionSymbol> preds = prologProg.createSetOfAllPredicates();
        for (PrologClause clause : prologProg.getClauses()) {
            if (!clause.isLogicProgramCompatible(preds)) {
                return false;
            }
        }
        return true;
    }


    @Override
    protected Result processTriplesProblem(TriplesProblem tp, Abortion aborter)
    throws AbortionException {
        PrologProgram triples = tp.getTriples().copy();
        triples.flattenOutConjunctions();
        PrologProgram clauses = tp.getClauses().copy();
        clauses.flattenOutConjunctions();
        PrologProgram all = new PrologProgram();
        for (PrologClause c : triples.getClauses()) {
            all.addClause(c);
        }
        for (PrologClause c : clauses.getClauses()) {
            all.addClause(c);
        }

        UndefinedPredicateInTriplesTransformer.logger.log(Level.FINEST,"Dumping triples:\n"); //#
        UndefinedPredicateInTriplesTransformer.logger.log(Level.FINEST, triples.toString() + "\n"); //#
        UndefinedPredicateInTriplesTransformer.logger.log(Level.FINEST,"Dumping clauses:\n"); //#
        UndefinedPredicateInTriplesTransformer.logger.log(Level.FINEST, clauses.toString() + "\n"); //#

        if (!this.isLogicProgramCompatible(all)) {
            UndefinedPredicateInTriplesTransformer.logger.log(
                Level.FINE,
                "The triples and clauses do not only contain atoms.\n"
            );
            return ResultFactory.unsuccessful();
        }

        Set<FunctionSymbol> preds = all.createSetOfAllPredicates();
        preds.removeAll(all.createSetOfDefinedPredicates());
        if (preds.isEmpty()) {
            return ResultFactory.unsuccessful();
        }
        while(!preds.isEmpty()) {
            all = new PrologProgram();
            PrologProgram newTriples = new PrologProgram(),
            newClauses = new PrologProgram();
            for (PrologClause c : triples.getClauses()) {
                Set<FunctionSymbol> clausePreds = c.createSetOfAllPredicates();
                clausePreds.retainAll(preds);
                if (clausePreds.isEmpty()) {
                    all.addClause(c);
                    newTriples.addClause(c);
                }
            }
            for (PrologClause c : clauses.getClauses()) {
                Set<FunctionSymbol> clausePreds = c.createSetOfAllPredicates();
                clausePreds.retainAll(preds);
                if (clausePreds.isEmpty()) {
                    all.addClause(c);
                    newClauses.addClause(c);
                }
            }
            triples = newTriples;
            clauses = newClauses;
            preds = all.createSetOfAllPredicates();
            preds.removeAll(all.createSetOfDefinedPredicates());
        }
        return ResultFactory.proved(
            new TriplesProblem(
                triples,
                clauses,
                new Afs(tp.getAfs())
            ),
            YNMImplication.SOUND,
            new UndefinedPredicateInTriplesTransformerProof()
        );
    }

    @Override
    public boolean isTriplesApplicable(TriplesProblem pp) {
        return true;
    }

    /**
     * UndefinedPredicateInTriplesTransformerProof.<br><br>
     *
     * Created: Feb 16, 2010<br>
     * Last modified: Feb 16, 2010
     *
     * @author cryingshadow
     * @version $Id$
     */
    public class UndefinedPredicateInTriplesTransformerProof
    extends DefaultProof {

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Utility.VerbosityExportable#export(aprove.verification.oldframework.Utility.Export_Util, aprove.verification.oldframework.Utility.VerbosityLevel)
         */
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return
            "Deleted triples and predicates having undefined goals " +
            o.cite(Citation.DT09) +
            ".";
        }

    }

}
