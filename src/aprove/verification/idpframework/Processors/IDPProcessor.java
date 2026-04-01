package aprove.verification.idpframework.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import immutables.*;

/**
 * Base class for IDPProblem processors. Takes care of really simple cases.
 * @author noschinski
 */
public abstract class IDPProcessor<MarkMetaData extends Result, ProblemType extends IDPProblem> extends Processor.ProcessorSkeleton implements Mark<MarkMetaData> {

    private final Exportable longDescription;
    protected Mark<MarkMetaData> mark;

    protected IDPProcessor(final String description) {
        this.mark = this.getMark();
        this.longDescription = new ExportableString(description);
    }

    protected Mark<MarkMetaData> getMark() {
        return this;
    }

    /**
     * Process an IDP problem; called after the really simple cases are already
     * handled. For semantics see semantics of {@link Processor#process}
     * @param idp Basic Obligation
     */
    protected abstract MarkMetaData processIDPProblem(ProblemType idp, Abortion aborter)
            throws AbortionException;

    @Override
    public Result process(final BasicObligation o,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {
        final IDPProblem problem = (IDPProblem) o; // this cast will succeed (see isApplicable)
        // FIXME: We will probably have some simple abortion cases here
        // (cached, empty, ...) cf. QDPProblemProcessor
        if (this.mark != null) {
            final ImmutablePair<? extends Conjunction<IDPProblem>, ? extends Result> lastProcessResult =
                problem.getMarks().getMark(this.mark);
            if (lastProcessResult != null) {
                return lastProcessResult.y;
            }
        }

        final MarkMetaData result = this.processIDPProblem((ProblemType) problem, aborter);

        if (this.mark != null) {
            if (result.getStrategy().isFail()) {
                problem.getMarks().setMark(this.mark, new Conjunction<IDPProblem>(problem), result);
            } else if (!result.getStrategy().isNormal()) {
                final IDPProblem resultProblem =
                    (IDPProblem) ((BasicObligationNode) result.getObligationChild().getNewObligation()).getBasicObligation();

                problem.getMarks().setMark(this.mark, new Conjunction<IDPProblem>(resultProblem), result);
                problem.getMarks().copyCompatibleMarks(resultProblem, this.mark);

            }
        }
        return result;
    }

    @Override
    public boolean isApplicable(final BasicObligation o) {
        if (o instanceof IDPProblem) {
            final IDPProblem problem = (IDPProblem) o;
            if (this.mark != null) {
                final ImmutablePair<? extends Conjunction<IDPProblem>, ? extends MarkMetaData> lastProcessResult =
                    problem.getMarks().getMark(this.mark);
                if (lastProcessResult != null
                    && lastProcessResult.x.size() == 1
                    && lastProcessResult.x.iterator().next().equals(problem)) {
                    return false;
                }
            }
            return this.isIDPApplicable((IDPProblem) o);
        }
        return false;
    }

    /**
     * Is the IDP processor applicable to this idp?
     * @param idp Problem to check for applicability
     * @return True, iff the processor is applicable
     */
    public abstract boolean isIDPApplicable(IDPProblem idp);

}
