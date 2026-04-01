package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * The OrTransformer transforms all ; constructs in a PrologProgram.
 * <br><br>
 *
 * Created: Oct 5, 2006<br>
 * Last modified: Dec 06, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class OrTransformer extends PrologProblemProcessor {

    /**
     * OrTransformerProof.<br><br>
     *
     * Created: Oct 5, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    public class OrTransformerProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Transformed all or-constructs" + o.cite(Citation.PROLOG) + ".";
        }

    }

    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.PROLOGProblem.Processors");

    /**
     * @param head
     * @return
     */
    private static Pair<PrologTerm, PrologTerm> transform(final PrologTerm body) {
        if (body.isDisjunctionTerm() && !body.getArgument(0).isIf()) {
            return new Pair<PrologTerm, PrologTerm>(body.getArgument(0), body.getArgument(1));
        } else {
            boolean found = false;
            final List<PrologTerm> args1 = new ArrayList<PrologTerm>();
            final List<PrologTerm> args2 = new ArrayList<PrologTerm>();
            for (final PrologTerm arg : body.getArguments()) {
                if (!found && arg.hasDisjunction()) {
                    found = true;
                    final Pair<PrologTerm, PrologTerm> pair = OrTransformer.transform(arg);
                    args1.add(pair.x);
                    args2.add(pair.y);
                } else {
                    args1.add(arg);
                    args2.add(arg);
                }
            }
            return new Pair<PrologTerm, PrologTerm>(new PrologTerm(body.getName(), args1), new PrologTerm(
                body.getName(),
                args2));
        }
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getProgram().isCutFree(); // TODO check whether this condition is enough
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        if (pp.getProgram().hasDisjunction()) {
            final PrologProgram prog = pp.getProgram().copy();
            final List<PrologClause> clauses = prog.getClauses();
            while (prog.hasDisjunction()) {
                int pos = -1;
                for (int i = 0; i < clauses.size(); i++) {
                    final PrologClause clause = clauses.get(i);
                    final PrologTerm body = clause.getBody();
                    if (body != null && body.hasDisjunction()) {
                        pos = i;
                        break;
                    }
                }
                if (pos >= 0) {
                    final PrologClause clause = clauses.get(pos);
                    final PrologTerm head = clause.getHead();
                    final Pair<PrologTerm, PrologTerm> newBodies = OrTransformer.transform(clause.getBody());
                    clauses.remove(pos);
                    clauses.add(pos, new PrologClause(head, newBodies.y));
                    clauses.add(pos, new PrologClause(head, newBodies.x));
                }
            }
            return
                ResultFactory.proved(
                    new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                    YNMImplication.EQUIVALENT,
                    new OrTransformerProof()
                );
        } else {
            return ResultFactory.unsuccessful();
        }
    }

}
