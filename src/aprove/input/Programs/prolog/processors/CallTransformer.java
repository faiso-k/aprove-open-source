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
 * The CallTransformer transforms all call predicates in a PrologProgram.
 * <br><br>
 *
 * Created: Dec 02, 2010<br>
 * Last modified: Dec 02, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class CallTransformer extends PrologProblemProcessor {

    /**
     * CallTransformerProof.<br><br>
     *
     * Created: Oct 20, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    public class CallTransformerProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Transformed all call-constructs " + o.cite(Citation.PROLOG) + ".";
        }

    }

    /**
     * @param term
     * @param toAdd
     * @param fridge
     * @return
     */
    private static PrologTerm transform(
        final PrologTerm term,
        final List<PrologClause> toAdd,
        final FreshNameGenerator fridge)
    {
        if (term == null) {
            return null;
        } else if (term.isCall()) {
            final String callName = fridge.getFreshName("call", false);
            final PrologTerm callTerm = new PrologTerm(callName, term.createSetOfAllVariables());
            toAdd.add(new PrologClause(callTerm, term.getArgument(0)));
            return callTerm;
        } else if (term.isConstant() || term.isVariable()) {
            return term;
        } else {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            for (final PrologTerm arg : term.getArguments()) {
                args.add(CallTransformer.transform(arg, toAdd, fridge));
            }
            return new PrologTerm(term.getName(), args);
        }
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return true;
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        if (pp.getProgram().hasPredicate(PrologBuiltin.CALL_PREDICATE)) {
            final PrologProgram prog = pp.getProgram().copy();
            final Set<String> used = new LinkedHashSet<String>();
            used.addAll(prog.createSetOfAllSymbolNames());
            used.addAll(PrologBuiltins.BUILTIN_PREDICATE_NAMES);
            final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_FUNCS);
            while (prog.hasPredicate(PrologBuiltin.CALL_PREDICATE)) {
                final List<PrologClause> clauses = new ArrayList<PrologClause>();
                final List<PrologClause> toAdd = new ArrayList<PrologClause>();
                for (final PrologClause clause : prog.getClauses()) {
                    clauses.add(clause.replaceBody(CallTransformer.transform(clause.getBody(), toAdd, fridge)));
                }
                prog.getClauses().clear();
                prog.getClauses().addAll(clauses);
                prog.getClauses().addAll(toAdd);
            }
            return ResultFactory.proved(
                new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                YNMImplication.EQUIVALENT,
                new CallTransformerProof());
        } else {
            return ResultFactory.unsuccessful();
        }
    }

}
