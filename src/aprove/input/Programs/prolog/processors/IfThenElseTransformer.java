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
 * The IfThenElseTransformer transforms -> predicates in a
 * PrologProgram.<br><br>
 *
 * Created: Oct 20, 2006<br>
 * Last modified: Nov 14, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class IfThenElseTransformer extends PrologProblemProcessor {

    /**
     * IfThenElseTransformerProof.<br><br>
     *
     * Created: Oct 20, 2006<br>
     * Last modified: Oct 20, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    public class IfThenElseTransformerProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Transformed all if-then-else-constructs " + o.cite(Citation.PROLOG) + ".";
        }

    }

    /**
     * @param term The term to transform.
     * @param toAdd The addidtional clauses for the freshly introduced if-predicates.
     * @param fridge Fresh names come out of the fridge...
     * @return A term where all builtin if-constructs are transformed to ordinary predicate calls.
     */
    private static PrologTerm transform(
        final PrologTerm term,
        final List<PrologClause> toAdd,
        final FreshNameGenerator fridge)
    {
        if (term == null) {
            return null;
        } else if (term.isIf()) {
            final String ifName = fridge.getFreshName("if", false);
            final List<PrologTerm> conjuncts = new ArrayList<PrologTerm>();
            final PrologTerm ifTerm = new PrologTerm(ifName, term.createSetOfAllVariables());
            conjuncts.add(PrologTerms.createCall(term.getArgument(0)));
            conjuncts.add(PrologTerms.createCut());
            conjuncts.add(term.getArgument(1));
            toAdd.add(new PrologClause(ifTerm, PrologTerms.createConjunction(conjuncts)));
            return ifTerm;
        } else if (term.isDisjunctionTerm() && term.getArgument(0).isIf()) {
            final PrologTerm ifthen = term.getArgument(0);
            final String ifName = fridge.getFreshName("if", false);
            final List<PrologVariable> vars = new ArrayList<PrologVariable>(term.createSetOfAllVariables());
            final List<PrologTerm> args = new ArrayList<PrologTerm>(vars);
            final List<PrologTerm> conjuncts = new ArrayList<PrologTerm>();
            final PrologTerm ifTerm = new PrologTerm(ifName, args);
            conjuncts.add(PrologTerms.createCall(ifthen.getArgument(0)));
            conjuncts.add(PrologTerms.createCut());
            conjuncts.add(ifthen.getArgument(1));
            toAdd.add(new PrologClause(ifTerm, PrologTerms.createConjunction(conjuncts)));
            toAdd.add(new PrologClause(ifTerm, term.getArgument(1)));
            return ifTerm;
        } else if (term.isConstant() || term.isVariable()) {
            return term;
        } else {
            final List<PrologTerm> args = new ArrayList<PrologTerm>();
            for (final PrologTerm arg : term.getArguments()) {
                args.add(IfThenElseTransformer.transform(arg, toAdd, fridge));
            }
            return new PrologTerm(term.getName(), args);
        }
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getProgram().isCutFree();
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        if (pp.getProgram().hasPredicate(PrologBuiltin.IF_PREDICATE)) {
            final PrologProgram prog = pp.getProgram().copy();
            final Set<String> used = new LinkedHashSet<String>();
            used.addAll(prog.createSetOfAllSymbolNames());
            used.addAll(PrologBuiltins.BUILTIN_PREDICATE_NAMES);
            final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_FUNCS);
            while (prog.hasPredicate(PrologBuiltin.IF_PREDICATE)) {
                final List<PrologClause> toAdd = new ArrayList<PrologClause>();
                final List<PrologClause> clauses = new ArrayList<PrologClause>();
                for (final PrologClause clause : prog.getClauses()) {
                    clauses.add(clause.replaceBody(IfThenElseTransformer.transform(clause.getBody(), toAdd, fridge)));
                }
                final List<PrologClause> progClauses = prog.getClauses();
                progClauses.clear();
                progClauses.addAll(clauses);
                progClauses.addAll(toAdd);
            }
            return
                ResultFactory.proved(
                    new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                    YNMImplication.EQUIVALENT,
                    new IfThenElseTransformerProof()
                );
        } else {
            return ResultFactory.unsuccessful();
        }
    }

}
