package aprove.input.Programs.prolog.processors;

import java.util.*;

import aprove.input.Programs.prolog.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * The NoRecursionProver is successful if the PrologProgram does not contain
 * any recursive predicates (including built-ins).
 * <br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */
public class NoRecursionProver extends PrologProblemProcessor {

    private final boolean complexity;

    @ParamsViaArguments({"complexity" })
    public NoRecursionProver(final boolean complexity) {
        this.complexity = complexity;
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        switch (pp.getQuery().getPurpose()) {
        case TERMINATION:
        case COMPLEXITY:
            return true;
        default:
            return false;
        }
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        if (pp.getProgram().createMapOfRecursivePredicates().isEmpty()) {
            final Set<FunctionSymbol> preds = pp.getProgram().createSetOfAllPredicates();
            preds.retainAll(PrologBuiltins.RECURSIVE_BUILTIN_PREDICATES.keySet());
            if (preds.isEmpty()) {
                return ResultFactory.provedWithValue(
                    this.complexity ? ComplexityYNM.CONSTANT : YNM.YES,
                    new NoRecursionProof());
            }
        }
        return ResultFactory.unsuccessful();
    }

    /**
     * NoRecursionProof.<br><br>
     *
     * @author cryingshadow
     * @version $Id$
     */
    public class NoRecursionProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "The program does not contain any calls to recursive predicates " + o.cite(Citation.PROLOG) + ".";
        }

    }

}
