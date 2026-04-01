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
 * The NotTransformer transforms all \+ predicates in a PrologProgram.
 * <br><br>
 *
 * Created: Oct 20, 2006<br>
 * Last modified: Nov 14, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class NotTransformer extends PrologProblemProcessor {

    /**
     * NotTransformerProof.<br><br>
     *
     * Created: Oct 20, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    public class NotTransformerProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Transformed all not-constructs " + o.cite(Citation.PROLOG) + ".";
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
        } else if (term.isNot()) {
            final String notName = fridge.getFreshName("not", false);
            final List<PrologTerm> conjuncts = new ArrayList<PrologTerm>();
            final PrologTerm notTerm = new PrologTerm(notName, term.createSetOfAllVariables());
            conjuncts.add(PrologTerms.createCall(term.getArgument(0)));
            conjuncts.add(PrologTerms.createCut());
            conjuncts.add(PrologTerms.createFail());
            toAdd.add(new PrologClause(notTerm, PrologTerms.createConjunction(conjuncts)));
            toAdd.add(new PrologClause(notTerm, null));
            return notTerm;
        } else if (term.isConstant() || term.isVariable()) {
            return term;
        } else {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            for (final PrologTerm arg : term.getArguments()) {
                args.add(NotTransformer.transform(arg, toAdd, fridge));
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
        if (pp.getProgram().hasPredicate(PrologBuiltin.NOT_PREDICATE)) {
            final PrologProgram prog = pp.getProgram().copy();
            final Set<String> used = new LinkedHashSet<String>();
            used.addAll(prog.createSetOfAllSymbolNames());
            used.addAll(PrologBuiltins.BUILTIN_PREDICATE_NAMES);
            final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_FUNCS);
            final List<PrologClause> toAdd = new ArrayList<PrologClause>();
            final List<PrologClause> clauses = new ArrayList<PrologClause>();
            for (final PrologClause clause : prog.getClauses()) {
                clauses.add(clause.replaceBody(NotTransformer.transform(clause.getBody(), toAdd, fridge)));
            }
            clauses.addAll(toAdd);
            prog.getClauses().clear();
            prog.getClauses().addAll(clauses);
            return
                ResultFactory.proved(
                    new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                    YNMImplication.EQUIVALENT,
                    new NotTransformerProof()
                );
        } else {
            return ResultFactory.unsuccessful();
        }
    }

}
