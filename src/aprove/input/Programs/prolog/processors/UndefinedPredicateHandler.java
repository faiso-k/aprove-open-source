package aprove.input.Programs.prolog.processors;

import java.util.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * The UndefinedPredicateHandler adds facts for all undefined predicates
 * in a PrologProgram.<br><br>
 *
 * Created: Nov 3, 2006<br>
 * Last modified: Nov 14, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class UndefinedPredicateHandler extends PrologProblemProcessor {

    /**
     * UndefinedPredicateHandlerProof.<br><br>
     *
     * Created: Nov 14, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    public class UndefinedPredicateHandlerProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Added facts for all undefined predicates " + o.cite(Citation.PROLOG) + ".";
        }

    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getProgram().isCutFree() && pp.getQuery().getPurpose().equals(PrologPurpose.TERMINATION);
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        final PrologProgram prog = pp.getProgram().copy();
        final Set<FunctionSymbol> undefinedPredicates = prog.createSetOfAllPredicates();
        undefinedPredicates.removeAll(prog.createSetOfDefinedPredicates());
        if (!undefinedPredicates.isEmpty()) {
            final List<PrologClause> clauses = prog.getClauses();
            for (final FunctionSymbol predicate : undefinedPredicates) {
                final List<PrologTerm> args = new ArrayList<PrologTerm>();
                for (int i = 0; i < predicate.getArity(); i++) {
                    args.add(new PrologNonAbstractVariable("X" + i));
                }
                clauses.add(new PrologClause(new PrologTerm(predicate.getName(), args), null));
            }
            return ResultFactory.proved(
                new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                YNMImplication.SOUND,
                new UndefinedPredicateHandlerProof());
        }
        return ResultFactory.unsuccessful();
    }

}
