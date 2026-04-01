package aprove.verification.idpframework.Processors;

import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;

/**
 *
 * @author MP
 */
public abstract class TIDPProcessor<MarkMetaData extends Result> extends IDPProcessor<MarkMetaData, TIDPProblem> {

    protected TIDPProcessor(final String description) {
        super(description);
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return (idp instanceof TIDPProblem);
    }

}
