package aprove.input.Programs.triples.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.input.Programs.triples.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Transforms a TriplesProblem into a PrologProblem by taking the union of the triples and clauses in the
 * TriplesProblem as the program for the PrologProblem.
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class TriplesToLPTransformer extends TriplesProblemProcessor {

    /**
     * @author cryingshadow
     * Standard proof citing DT09.
     */
    public class TriplesToLPProof extends Proof.DefaultProof {

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Utility.VerbosityExportable#export(aprove.prooftree.Export.Utility.Export_Util, aprove.verification.oldframework.Utility.VerbosityLevel)
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return o.export("We consider the union of DTs and clauses as a logic program ")
                + o.cite(Citation.DT09)
                + o.export(".");
        }
    }

    /**
     * The standard logger for this processor.
     */
    protected static final Logger LOG = Logger
        .getLogger("aprove.input.Programs.triples.processors.TriplesToLPTransformer");

    /* (non-Javadoc)
     * @see aprove.input.Programs.triples.processors.TriplesProblemProcessor#isTriplesApplicable(aprove.input.Programs.triples.TriplesProblem)
     */
    @Override
    public boolean isTriplesApplicable(final TriplesProblem pp) {
        return true;
    }

    @Override
    protected Result processTriplesProblem(final TriplesProblem tp, final Abortion aborter) throws AbortionException {
        final PrologProgram triples = tp.getTriples().copy();
        triples.flattenOutConjunctions();
        triples.transformUnderscores();
        final PrologProgram clauses = tp.getClauses().copy();
        clauses.flattenOutConjunctions();
        clauses.transformUnderscores();
        final PrologProgram all = new PrologProgram();
        for (final PrologClause c : triples.getClauses()) {
            all.addClause(c);
        }
        for (final PrologClause c : clauses.getClauses()) {
            all.addClause(c);
        }
        final Set<PrologProblem> todo = new LinkedHashSet<PrologProblem>();
        for (final Triple<FunctionSymbol, YNM[], Boolean> triple : tp.getAfs().getFilterings()) {
            todo.add(
                new PrologProblem(
                    all,
                    new PrologQuery(triple.x.getName(), triple.y, PrologPurpose.TERMINATION),
                    PrologProblem.DEFAULT_SMT_FACTORY,
                    PrologProblem.DEFAULT_SMT_LOGIC
                )
            );
        }
        TriplesToLPTransformer.LOG.log(Level.FINEST, "Dumping triples:\n");
        TriplesToLPTransformer.LOG.log(Level.FINEST, triples.toString() + "\n");
        TriplesToLPTransformer.LOG.log(Level.FINEST, "Dumping clauses:\n");
        TriplesToLPTransformer.LOG.log(Level.FINEST, clauses.toString() + "\n");

        if (!PrologProgram.isLogicProgram(all)) {
            TriplesToLPTransformer.LOG.log(
                Level.FINE,
                "The triples and clauses do not form a definite logic program.\n");
            return ResultFactory.unsuccessful();
        }

        return ResultFactory.provedAnd(todo, YNMImplication.SOUND, new TriplesToLPProof());
    }

}
