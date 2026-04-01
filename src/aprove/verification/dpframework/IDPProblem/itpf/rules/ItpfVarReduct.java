package aprove.verification.dpframework.IDPProblem.itpf.rules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 *
 * @author mpluecke
 */
public class ItpfVarReduct extends IItpfRule.ItpfRuleSkeleton {

    private ExportableString longDescription;
    private ExportableString shortDescription;

    public ItpfVarReduct() {
        this.shortDescription = this.longDescription = new ExportableString("ItpfVarReduct");
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
        return idp.getRuleAnalysis().isNfQSubsetEqNfR();
    }

    @Override
    public boolean isApplicable(IDPProblem idp, Itpf formula, ApplicationMode mode) {
        return idp.getRuleAnalysis().isNfQSubsetEqNfR();
    }


    @Override
    public Itpf process(IDPProblem idp, Itpf formula, ApplicationMode mode,
            Abortion aborter) throws AbortionException {
        VarReductVisitor visitor = new VarReductVisitor(idp.getRuleAnalysis(), mode);
        return visitor.applyTo(formula.normalize());
    }

    protected static class VarReductVisitor extends IItpfVisitor.ItpfVisitorSkeleton<Object> {

        private final IDPRuleAnalysis rules;

        public VarReductVisitor(IDPRuleAnalysis rules, ApplicationMode mode) {
            super(ItpfMark.ItpfVarReduct, mode);
            this.rules =rules;
        }

        @Override
        public Itpf caseItp(final ItpfItp tp) {
            if (tp.getRelation() == ItpRelation.TO_TRANS) {
                TRSTerm l = tp.getL();
                if (!tp.getS().containsAll(l.getVariables())) {
                    return this.mark(tp, tp);
                }
                Set<FunctionSymbol> definedSymbols = this.rules.getDefinedSymbols();
                for (FunctionSymbol fs : l.getFunctionSymbols()) {
                    if (definedSymbols.contains(fs)) {
                        return this.mark(tp, tp);
                    }
                }
                TRSTerm r = tp.getR();
                if (!l.unifies(r)) {
                    return this.mark(tp, ItpfItp.create(l, tp.getKLeft(), tp.getContextL(), ItpRelation.EQ, r, tp.getKRight(), tp.getContextR(), tp.getS()));
                }
            } else if (tp.getRelation() == ItpRelation.TO_PLUS || tp.getRelation() == ItpRelation.TO) {
                TRSTerm l = tp.getL();
                if (l.isVariable() && tp.getS().contains(l)) {
                    return Itpf.FALSE;
                }
            }
            return this.mark(tp, tp);
        }

    }

}
