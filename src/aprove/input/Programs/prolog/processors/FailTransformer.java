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
 * The FailTransformer transforms all fail predicates in a PrologProgram.
 * <br><br>
 *
 * Created: Dec 02, 2010<br>
 * Last modified: Dec 02, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class FailTransformer extends PrologProblemProcessor {

    /**
     * FailTransformerProof.<br><br>
     *
     * Created: Oct 20, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    public class FailTransformerProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Added clauses for the built-in fail predicate " + o.cite(Citation.PROLOG) + ".";
        }

    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return true;
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        final PrologProgram prog = pp.getProgram().copy();
        final Set<String> used = new LinkedHashSet<String>();
        used.addAll(prog.createSetOfAllSymbolNames());
        used.addAll(PrologBuiltins.BUILTIN_PREDICATE_NAMES);
        final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_FUNCS);
        if (prog.hasPredicate(PrologBuiltin.FAIL_PREDICATE) && !prog.isDefined(PrologBuiltin.FAIL_PREDICATE)) {
            final List<PrologTerm> args1 = new ArrayList<PrologTerm>();
            args1.add(new PrologTerm("a"));
            final List<PrologTerm> args2 = new ArrayList<PrologTerm>();
            args2.add(new PrologTerm("b"));
            final PrologTerm failTermA = new PrologTerm(fridge.getFreshName("failure", true), args1);
            final PrologTerm failTermB = new PrologTerm(fridge.getFreshName("failure", true), args2);
            prog.addClause(new PrologClause(PrologTerms.createFail(), failTermA));
            prog.addClause(new PrologClause(failTermB, null));
            return
                ResultFactory.proved(
                    new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                    YNMImplication.EQUIVALENT,
                    new FailTransformerProof()
                );
        }
        return ResultFactory.unsuccessful();
    }

}
