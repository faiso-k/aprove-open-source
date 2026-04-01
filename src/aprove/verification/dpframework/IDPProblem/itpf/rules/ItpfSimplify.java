package aprove.verification.dpframework.IDPProblem.itpf.rules;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;

/**
 *
 * @author mpluecke
 */
public class ItpfSimplify extends IItpfRule.ItpfRuleSkeleton  {

    private ExportableString longDescription;
    private ExportableString shortDescription;

    public ItpfSimplify() {
        this.shortDescription = this.longDescription = new ExportableString("ItpfSimplify");
    }


    @Override
    public Exportable getDescription(NameLength length) {
        switch (length) {
        case SHORT :
            return this.shortDescription;
        case LONG :
            return this.longDescription;
        }
        return null;
    }


    @Override
    public boolean isApplicable(IDPProblem idp) {
        return true;
    }

    @Override
    public boolean isApplicable(IDPProblem idp, Itpf formula, ApplicationMode mode) {
        return true;
    }


    @Override
    public Itpf process(IDPProblem idp, Itpf formula, ApplicationMode mode,
            Abortion aborter) throws AbortionException {
        return formula.normalize();
    }

}
