package aprove.input.Programs.prolog.processors;

import java.util.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * The UnifyTransformer transforms all = predicates in a PrologProgram.
 * <br><br>
 *
 * Created: Dec 02, 2010<br>
 * Last modified: Dec 02, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class UnifyTransformer extends PrologProblemProcessor {

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return true;
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        final PrologProgram prog = pp.getProgram().copy();
        if (prog.hasPredicate(PrologBuiltin.UNIFY_PREDICATE) && !prog.isDefined(PrologBuiltin.UNIFY_PREDICATE)) {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            args.add(new PrologNonAbstractVariable("X"));
            args.add(new PrologNonAbstractVariable("X"));
            prog.addClause(new PrologClause(new PrologTerm(PrologBuiltin.UNIFY_NAME, args), null));
            return ResultFactory.proved(
                new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                YNMImplication.EQUIVALENT,
                new UnifyTransformerProof());
        }
        return ResultFactory.unsuccessful();
    }

    /**
     * UnifyTransformerProof.<br><br>
     *
     * Created: Oct 20, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    public class UnifyTransformerProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Added a fact for the built-in = predicate " + o.cite(Citation.PROLOG) + ".";
        }

    }

}
