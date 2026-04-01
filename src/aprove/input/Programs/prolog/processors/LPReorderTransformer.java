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
 * The LPReorderTransformer moves all facts to the beginning in a definite LP.
 * <br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class LPReorderTransformer extends PrologProblemProcessor {

    /**
     * LPReorderTransformerProof.<br><br>
     *
     * @author cryingshadow
     * @version $Id$
     */
    public static class LPReorderTransformerProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Reordered facts before rules in definite LP " + o.cite(Citation.PROLOG) + ".";
        }

    }

    /**
     * @param p The program to reorder.
     * @return The reordered program.
     */
    public static PrologProgram reorder(final PrologProgram p) {
        final PrologProgram prog = p.copy();
        final List<PrologClause> facts = new ArrayList<PrologClause>();
        final List<PrologClause> rules = new ArrayList<PrologClause>();
        for (final PrologClause clause : prog.getClauses()) {
            if (clause.isFact()) {
                facts.add(clause);
            } else {
                rules.add(clause);
            }
        }
        prog.getClauses().clear();
        for (final PrologClause fact : facts) {
            prog.addClause(fact);
        }
        for (final PrologClause rule : rules) {
            prog.addClause(rule);
        }
        return prog;
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return PrologPurpose.isRuntimeAnalysis(pp.getQuery().getPurpose())
            && PrologProgram.isLogicProgram(pp.getProgram())
            && pp.getProgram().hasFactAfterRule();
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        final PrologProgram prog = LPReorderTransformer.reorder(pp.getProgram());
        return
            ResultFactory.proved(
                new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                YNMImplication.EQUIVALENT,
                new LPReorderTransformerProof()
            );
    }

}
