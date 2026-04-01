package aprove.verification.dpframework.IDPProblem.itpf.rules;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;

/**
 *
 * @author mpluecke
 */
public class ItpfStepDetect extends IItpfRule.ItpfRuleSkeleton {

    private ExportableString longDescription;
    private ExportableString shortDescription;

    public ItpfStepDetect() {
        this.shortDescription = this.longDescription = new ExportableString("ItpfStepDetect");
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
        StepDetectVisitor visitor = new StepDetectVisitor(mode);
        return visitor.applyTo(formula);
    }

    protected static class StepDetectVisitor extends IItpfVisitor.ItpfVisitorSkeleton<Object> {

        public StepDetectVisitor(ApplicationMode mode) {
            super(ItpfMark.ItpfStepDetect, mode);
        }

        @Override
        public Itpf caseItp(ItpfItp tp) {
            if (tp.getRelation() == ItpRelation.TO_TRANS) {
                TRSTerm l = tp.getL();
                TRSTerm r = tp.getR();
                if (!l.unifies(r)) {
                    return this.mark(tp, ItpfItp.create(l, tp.getKLeft(), tp.getContextL(), ItpRelation.TO_PLUS, r, tp.getKRight(), tp.getContextR(), tp.getS()));
                }
            }
            return this.mark(tp, tp);
        }

    }

}
