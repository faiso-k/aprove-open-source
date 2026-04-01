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
 * The CutEliminator removes all cuts from a PrologProgram.<br><br>
 *
 * Created: Oct 20, 2006<br>
 * Last modified: Nov 14, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class CutEliminator extends PrologProblemProcessor {

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return true;
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        final PrologProgram oldProg = pp.getProgram();
        if (!oldProg.isCutFree()) {
            final PrologProgram prog = pp.getProgram().copy();
            final List<PrologClause> clauses = prog.getClauses();
            clauses.clear();
            // we delete all cuts from the program
            for (final PrologClause clause : oldProg.getClauses()) {
                clauses.add(clause.replaceBody(CutEliminator.deleteCutsFromBody(clause.getBody())));
            }
            return
                ResultFactory.proved(
                    new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                    YNMImplication.SOUND,
                    new CutEliminatorProof()
                );
        }
        return ResultFactory.unsuccessful();
    }

    private static PrologTerm deleteCutsFromBody(final PrologTerm body) {
        if (body == null || body.isCut()) {
            return null;
        } else if (body.isConjunction()) {
            final PrologTerm left = body.getArgument(0), right = body.getArgument(1);
            if (left.isCut()) {
                if (right.isCut()) {
                    return PrologTerms.createTrue();
                } else {
                    return CutEliminator.deleteCutsFromBody(right);
                }
            } else if (right.isCut()) {
                return CutEliminator.deleteCutsFromBody(left);
            } else {
                final PrologTerm arg1 = CutEliminator.deleteCutsFromBody(left), arg2 =
                    CutEliminator.deleteCutsFromBody(right);
                if (arg1.isTrue()) {
                    if (arg2.isTrue()) {
                        return PrologTerms.createTrue();
                    } else {
                        return arg2;
                    }
                } else if (arg2.isTrue()) {
                    return arg1;
                } else {
                    return PrologTerms.createConjunction(arg1, arg2);
                }
            }
        } else if (body.isDisjunctionTerm()) {
            final PrologTerm left = body.getArgument(0), right = body.getArgument(1);
            PrologTerm arg1, arg2;
            if (left.isCut()) {
                arg1 = PrologTerms.createTrue();
            } else {
                arg1 = CutEliminator.deleteCutsFromBody(left);
            }
            if (right.isCut()) {
                arg2 = PrologTerms.createTrue();
            } else {
                arg2 = CutEliminator.deleteCutsFromBody(right);
            }
            return PrologTerms.createDisjunction(arg1, arg2);
        } else if (body.isIf()) {
            final PrologTerm left = body.getArgument(0), right = body.getArgument(1);
            PrologTerm arg1, arg2;
            if (left.isCut()) {
                arg1 = PrologTerms.createTrue();
            } else {
                arg1 = CutEliminator.deleteCutsFromBody(left);
            }
            if (right.isCut()) {
                arg2 = PrologTerms.createTrue();
            } else {
                arg2 = CutEliminator.deleteCutsFromBody(right);
            }
            return PrologTerms.createIf(arg1, arg2);
        } else {
            return body;
        }
    }

    /**
     * CutEliminatorProof.<br><br>
     *
     * Created: Oct 20, 2006<br>
     * Last modified: Nov 14, 2006
     *
     * @author cryingshadow
     * @version $Id$
     */
    public class CutEliminatorProof extends DefaultProof {

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Eliminated all cuts by simply ignoring them" + o.cite(Citation.PROLOG) + ".";
        }

    }

}
