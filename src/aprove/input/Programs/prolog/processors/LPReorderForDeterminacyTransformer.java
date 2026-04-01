package aprove.input.Programs.prolog.processors;

import java.util.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;

/**
 * The LPReorderTransformer moves all facts to the beginning in a definite LP.
 * <br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */
@NoParams
public class LPReorderForDeterminacyTransformer extends PrologProblemProcessor {

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getQuery().getPurpose() == PrologPurpose.DETERMINACY
            && PrologProgram.isLogicProgram(pp.getProgram())
            && pp.getProgram().hasFactAfterRule();
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        final PrologProgram prog = LPReorderTransformer.reorder(pp.getProgram());
        final Set<PrologProblem> obls = new LinkedHashSet<PrologProblem>();
        obls.add(new PrologProblem(prog, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()));
        obls.add(
            new PrologProblem(
                prog,
                pp.getQuery().setPurpose(PrologPurpose.TERMINATION),
                pp.getSMTFactory(),
                pp.getSMTLogic()
            )
        );
        return
            ResultFactory.provedAnd(obls, YNMImplication.SOUND, new LPReorderTransformer.LPReorderTransformerProof());
    }

}
