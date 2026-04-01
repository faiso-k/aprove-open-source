package aprove.verification.dpframework.IDPProblem.itpf.rules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 *
 * @author mpluecke
 */
public class ItpfUnify extends IItpfRule.ItpfRuleSkeleton {

    private ExportableString longDescription;
    private ExportableString shortDescription;

    public ItpfUnify() {
        this.shortDescription = this.longDescription = new ExportableString("ItpfUnify");
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
        UnifyVisitor visitor = new UnifyVisitor(mode);
        return visitor.applyTo(formula.normalize());
    }

    protected static class UnifyVisitor extends IItpfVisitor.ItpfVisitorSkeleton<Object> {

        public UnifyVisitor(ApplicationMode mode) {
            super(ItpfMark.ItpfUnify, mode);
        }

        @Override
        public Itpf caseAnd(ItpfAnd and, ImmutableSet<? extends Itpf> newChildren){
            // instantiate
            Map<TRSVariable, TRSTerm> subst = new LinkedHashMap<TRSVariable, TRSTerm>();
            for (Itpf newChild : newChildren) {
                if (newChild.isItp()) {
                    ItpfItp itp = (ItpfItp) newChild;
                    if (itp.getRelation() == ItpRelation.EQ && itp.getL().isVariable()) {
                        subst.put((TRSVariable) itp.getL(), itp.getR());
                    }
                }
            }
            if (subst.size() > 0) {
                TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(subst));
                Set<Itpf> substNewChildren = new LinkedHashSet<Itpf>();
                for (Itpf newChild : newChildren) {
                    substNewChildren.add(newChild.applySubstitution(sigma));
                }
                newChildren = ImmutableCreator.create(substNewChildren);
            }
            return super.caseAnd(and, newChildren);
        }

        @Override
        public Itpf caseItp(final ItpfItp tp) {
            if (tp.getRelation() == ItpRelation.EQ) {
                TRSTerm l = tp.getL();
                TRSTerm r = tp.getR();
                if (l.isVariable()) {
                    if (r.isVariable()) {
                        // nothing to do here
                    } else {
                        if (((TRSFunctionApplication) r).getVariables().contains(r)) {
                            // occur failure
                            this.applicationCount++;
                            return Itpf.FALSE;
                        }
                    }
                } else {
                    if (r.isVariable()) {
                        // swap
                        this.applicationCount++;
                        return this.mark(tp, ItpfItp.create(tp.getR(), tp.getKRight(), tp.getContextR(), ItpRelation.EQ, tp.getL(), tp.getKLeft(), tp.getContextL(), tp.getS()));
                    } else {
                        TRSFunctionApplication fl = (TRSFunctionApplication) l;
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
                                children.add(this.mark(tp, ItpfItp.create(fl.getArgument(i), tp.getKLeft(), contextL, ItpRelation.EQ, fr.getArgument(i), tp.getKRight(), contextR, tp.getS())));
                            }
                            this.applicationCount++;
                            return this.mark(tp, ItpfAnd.create(ImmutableCreator.create(children)));
                        }
                    }
                }
            }
            return this.mark(tp, tp);
        }

        @Override
        protected Itpf mark(Itpf origItpf, Itpf newItpf) {
            // do not mark until unchanged
            if (origItpf != newItpf) {
                origItpf.copyCompatibleMarks(newItpf, this.mark);
                return newItpf;
            } else {
                return super.mark(origItpf, newItpf);
            }
        }

    }

}
