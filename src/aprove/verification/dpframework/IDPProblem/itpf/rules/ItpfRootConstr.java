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
import immutables.*;

/**
 *
 * @author mpluecke
 */
public class ItpfRootConstr extends IItpfRule.ItpfRuleSkeleton implements IInitialItpfRule {

    private ExportableString longDescription;
    private ExportableString shortDescription;

    public ItpfRootConstr() {
        this.shortDescription = this.longDescription = new ExportableString("ItpfRootConstr");
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
        RootConstrVisitor visitor = new RootConstrVisitor(idp.getRuleAnalysis(), mode);
        return visitor.applyTo(formula.normalize());
    }

    @Override
    public Itpf processInitial(IDPRuleAnalysis ruleAnalysis, Itpf formula,
            Abortion aborter) throws AbortionException {
        RootConstrVisitor visitor = new RootConstrVisitor(ruleAnalysis, ApplicationMode.Multistep);
        return visitor.applyTo(formula.normalize());
    }


    protected static class RootConstrVisitor extends IItpfVisitor.ItpfVisitorSkeleton<Object> {

        private final IDPRuleAnalysis ruleAnalysis;

        public RootConstrVisitor(IDPRuleAnalysis ruleAnalysis, ApplicationMode mode) {
            super(ItpfMark.RootConstr, mode);
            this.ruleAnalysis = ruleAnalysis;
        }

        @Override
        public Itpf caseItp(final ItpfItp tp) {
            if (tp.getRelation() == ItpRelation.TO || tp.getRelation() == ItpRelation.TO_TRANS || tp.getRelation() == ItpRelation.TO_PLUS) {
                TRSTerm l = tp.getL();
                TRSTerm r = tp.getR();
                if (!l.isVariable() && !r.isVariable()) {
                    TRSFunctionApplication fl = (TRSFunctionApplication) l;
                    if (!this.ruleAnalysis.getPreDefinedMap().isPredefined(fl.getRootSymbol()) && !this.ruleAnalysis.getRAnalysis().getDefinedSymbols().contains(fl.getRootSymbol())) {
                        TRSFunctionApplication fr = (TRSFunctionApplication) r;
                        if (!fl.getRootSymbol().equals(fr.getRootSymbol())) {
                            // clash failure
                            this.applicationCount++;
                            return Itpf.FALSE;
                        } else {
                            // reduce function symbol
                            Set<Itpf> children = new LinkedHashSet<Itpf>();
                            FunctionSymbol rootL = fl.getRootSymbol();
                            FunctionSymbol rootR = fr.getRootSymbol();
                            int arity = rootL.getArity();
                            for (int i = 0; i < arity; i++) {
                                ImmutableList<ImmutablePair<FunctionSymbol, Integer>> contextL = null;
                                if (tp.getContextL() != null) {
                                    List<ImmutablePair<FunctionSymbol, Integer>> contextLMut = new ArrayList<ImmutablePair<FunctionSymbol, Integer>>(tp.getContextL());
                                    contextLMut.add(new ImmutablePair<FunctionSymbol, Integer>(rootL, i));
                                    contextL = ImmutableCreator.create(contextLMut);
                                }
                                ImmutableList<ImmutablePair<FunctionSymbol, Integer>> contextR = null;
                                if (tp.getContextR() != null) {
                                    List<ImmutablePair<FunctionSymbol, Integer>> contextRMut = new ArrayList<ImmutablePair<FunctionSymbol, Integer>>(tp.getContextR());
                                    contextRMut.add(new ImmutablePair<FunctionSymbol, Integer>(rootR, i));
                                    contextR = ImmutableCreator.create(contextRMut);
                                }
                                Itpf newChild = ItpfItp.create(fl.getArgument(i), tp.getKLeft(), contextL, ItpRelation.TO_TRANS, fr.getArgument(i), tp.getKRight(), contextR, tp.getS());
                                newChild = this.applyTo(this.mark(tp, newChild));
                                children.add(newChild);
                            }
                            this.applicationCount++;
                            return this.mark(tp, ItpfAnd.create(ImmutableCreator.create(children)));
                        }
                    }
                }
            }
            return this.mark(tp, tp);
        }

    }


}
