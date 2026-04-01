package aprove.verification.idpframework.Processors.ItpfRules;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;

/**
 *
 * @author MP
 */
public abstract class ContextFreeItpfReplaceRule extends AbstractItpfReplaceRule.ItpfReplaceRuleSkeleton<ReplaceContext.ReplaceContextSkeleton, Unused> {

    public ContextFreeItpfReplaceRule(final ExportableString shortDescription,
            final ExportableString longDescription) {
        super(shortDescription, longDescription);
    }

    @Override
    protected final ReplaceContext.ReplaceContextSkeleton createContext(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return new ReplaceContext.ReplaceContextSkeleton();
    }

}
