package aprove.verification.dpframework.IDPProblem.itpf.rules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Docu-guess (fuhs):
 * Transforms e.g. "(s >= t AND u > v)  ->^*  TRUE" to
 * "(s >= t ->^* TRUE)  AND  (u > v ->^* TRUE)", i.e.,
 * lifts junctors over rewrite relation constraints.
 *
 * @author mpluecke
 */
public class ItpfBoolOp extends IItpfRule.ItpfRuleSkeleton {

    private ExportableString longDescription;
    private ExportableString shortDescription;

    public ItpfBoolOp() {
        this.shortDescription = this.longDescription = new ExportableString("ItpfBoolOp");
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
        BoolOpVisitor visitor = new BoolOpVisitor(idp.getRuleAnalysis().getPreDefinedMap(), mode);
        return visitor.applyTo(formula.normalize());
    }

    protected static class BoolOpVisitor extends IItpfVisitor.ItpfVisitorSkeleton<Object> {

        private final IDPPredefinedMap predefinedMap;


        public BoolOpVisitor(IDPPredefinedMap predefinedMap, ApplicationMode mode) {
            super(ItpfMark.ItpfBoolOp, mode);
            this.predefinedMap = predefinedMap;
        }

        @Override
        public Itpf caseItp(ItpfItp tp) {
            Itpf res;
            if ((tp.getRelation() == ItpRelation.TO || tp.getRelation() == ItpRelation.TO_PLUS || tp.getRelation() == ItpRelation.TO_TRANS) &&
                    tp.getKLeft() == null && tp.getKRight() == null) {
                res = this.applyToPair(tp.getL(), tp.getR(), tp.getRelation(), tp.getS(), true, tp);
            } else {
                res = tp;
            }
            return this.mark(tp, res);
        }

        /**
         *
         * @param l
         * @param r must be TRUE or FALSE
         * @param rel current relation
         * @param S the S set for the ItpItp's
         * @param orig the original Itp
         * @return orig itpf iff no boolean combination was found in firstCall, new itpf otherwise
         */
        protected Itpf applyToPair(TRSTerm l, TRSTerm r, ItpRelation rel, ImmutableSet<TRSTerm> S, boolean isFirstCall, ItpfItp orig) {
            if (!l.isVariable() && !r.isVariable()) {
                TRSFunctionApplication fl = (TRSFunctionApplication) l;
                FunctionSymbol leftRoot = fl.getRootSymbol();
                PredefinedFunction func = this.predefinedMap.getPredefinedFunction(leftRoot);
                if (func != null && func.isBoolean()) {
                    TRSFunctionApplication fr = (TRSFunctionApplication) r;
                    ItpRelation newRel = this.newRel(rel);
                    if (this.predefinedMap.isBooleanTrue(fr.getRootSymbol())) {
                        // r == TRUE
                        switch (func.getFunc()) {
                            case Land : {
                                Set<Itpf> children = new LinkedHashSet<Itpf>();
                                children.add(this.applyToPair(fl.getArgument(0), r, newRel, S, false, orig));
                                children.add(this.applyToPair(fl.getArgument(1), r, newRel, S, false, orig));
                                return this.mark(orig, ItpfAnd.create(ImmutableCreator.create(children)));
                            }
                            case Lor : {
                                Set<Itpf> children = new LinkedHashSet<Itpf>();
                                children.add(this.applyToPair(fl.getArgument(0), r, newRel, S, false, orig));
                                children.add(this.applyToPair(fl.getArgument(1), r, newRel, S, false, orig));
                                return this.mark(orig, ItpfOr.create(ImmutableCreator.create(children)));
                            }
                            case Lnot :
                                return this.applyToPair(fl.getArgument(0), this.predefinedMap.getBooleanFalse().getTerm(), newRel, S, false, orig);
                        }
                    } else  {
                        // r == FALSE
                        switch (func.getFunc()) {
                            case Land : {
                                Set<Itpf> children = new LinkedHashSet<Itpf>();
                                children.add(this.applyToPair(fl.getArgument(0), r, newRel, S, false, orig));
                                children.add(this.applyToPair(fl.getArgument(1), r, newRel, S, false, orig));
                                return this.mark(orig, ItpfOr.create(ImmutableCreator.create(children)));
                            }
                            case Lor : {
                                Set<Itpf> children = new LinkedHashSet<Itpf>();
                                children.add(this.applyToPair(fl.getArgument(0), r, newRel, S, false, orig));
                                children.add(this.applyToPair(fl.getArgument(1), r, newRel, S, false, orig));
                                return this.mark(orig, ItpfAnd.create(ImmutableCreator.create(children)));
                            }
                            case Lnot :
                                return this.applyToPair(fl.getArgument(0), this.predefinedMap.getBooleanTrue().getTerm(), newRel, S, false, orig);
                        }
                    }
                }
            }
            return isFirstCall ? this.mark(orig, orig) : this.mark(orig, ItpfItp.create(l, rel, r, S));
        }


        protected ItpRelation newRel(ItpRelation rel) {
            switch (rel) {
            case TO : return ItpRelation.EQ;
            default : return ItpRelation.TO_TRANS;
            }
        }
    }

}
