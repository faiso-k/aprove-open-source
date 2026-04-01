package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * The BuiltinConflictTransformer freshly renames predicates which have
 * declaring clauses, but have the same name and arity as one of the
 * built-in predicates.<br><br>
 *
 * Created: Oct 23, 2006<br>
 * Last modified: May 31, 2011
 *
 * @author cryingshadow
 * @version $Id$
 */
public class BuiltinConflictTransformer extends PrologProblemProcessor {

    private final boolean complexity;

    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.PROLOGProblem.Processors");

    @ParamsViaArguments({"complexity" })
    public BuiltinConflictTransformer(final boolean complexity) {
        this.complexity = complexity;
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return true;
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        final PrologProgram prog = pp.getProgram().copy();
        final Set<FunctionSymbol> predicates = prog.createSetOfDefinedPredicates();
        predicates.retainAll(PrologBuiltins.BUILTIN_PREDICATES);
        prog.getClauses().clear();
        if (!predicates.isEmpty()) {
            final PrologFNG fridge =
                new PrologFNG(BuiltinConflictTransformer.getConflictNames(prog), FreshNameGenerator.PROLOG_FUNCS);
            for (final PrologClause clause : pp.getProgram().getClauses()) {
                prog.addClause(clause.walkAll(new ReplacementWalker() {

                    @Override
                    public boolean goDeeper(final PrologTerm term) {
                        return true;
                    }

                    @Override
                    public boolean isApplicable(final PrologTerm term) {
                        return term != null && predicates.contains(term.createFunctionSymbol());
                    }

                    @Override
                    public PrologTerm replace(final PrologTerm term) {
                        return term.replaceName(fridge.getFreshName("user_defined_" + term.getName(), true));
                    }

                }));
            }
            return
                ResultFactory.proved(
                    new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                    (this.complexity ? BothBounds.create() : YNMImplication.EQUIVALENT),
                    new BuiltinConflictTransformerProof()
                );
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    /**
     * Creates a set containing all names which may cause a conflict
     * when adding definitions for built-in predicates.
     * @return A set with all conflicting predicate names.
     */
    private static Set<String> getConflictNames(final PrologProgram prog) {
        final Set<String> used = new LinkedHashSet<String>();
        for (final FunctionSymbol sym : prog.createSetOfAllFunctionSymbols()) {
            used.add(sym.getName());
        }
        used.addAll(PrologBuiltins.BUILTIN_PREDICATE_NAMES);
        return used;
    }

    /**
     * BuiltinConflictTransformerProof.<br><br>
     *
     * Created: Nov 14, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    public class BuiltinConflictTransformerProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Renamed defined predicates conflicting with built-in predicates " + o.cite(Citation.PROLOG) + ".";
        }

    }

}
