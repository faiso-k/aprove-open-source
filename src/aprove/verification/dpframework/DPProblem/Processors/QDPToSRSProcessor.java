package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

public class QDPToSRSProcessor extends QDPProblemProcessor {

    // true: consider input to be in form for Zantema QDP -> SRS transformation
    // false: assuming a maximum signature arity of 1, just make the elements
    //        of P elements of R and hence obtain a SRS
    private final boolean zantema;

    @ParamsViaArgumentObject
    public QDPToSRSProcessor(final Arguments arguments) {
        this.zantema = arguments.zantema;
    }

    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        QTRSProblem srs;
        if (this.zantema) {
            srs = this.zantemaToSRS(qdp);
            if (srs == null) {
                srs = this.dualZantemaToSRS(qdp);
            }
        }
        else {
            srs = QDPToSRSProcessor.plainToSRS(qdp, aborter);
        }
        if (srs == null) {
            if (Globals.useAssertions) {
                assert this.zantema;
            }
            return ResultFactory.notApplicable();
        }
        return ResultFactory.proved(srs, YNMImplication.SOUND, new QDPToSRSProof(qdp, srs, this.zantema));
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        if (this.zantema && Options.certifier.isCeta()) {
            return false;
        }
        if (this.zantema) {
            return qdp.getR().isEmpty();
        }
        else {
            return qdp.getMaxArity() <= 1;
            // TODO only consider PRsignature for maxArity, disregard Q
        }
    }

    public QTRSProblem zantemaToSRS(final QDPProblem qdp) {
        if (Globals.useAssertions) {
            assert(qdp.getR().isEmpty());
        }
        final Set<Rule> P = qdp.getP();
        if (P.size() < 2) {return null;}
        FunctionSymbol binary = null;
        final Set<FunctionSymbol> sigmaP = new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> sigmaPprime = new LinkedHashSet<FunctionSymbol>();
        final Set<Rule> srs = new LinkedHashSet<Rule>();
        for (final Rule dp : P) {
            final TRSFunctionApplication left = dp.getLeft();
            final TRSTerm right = dp.getRight();
            FunctionSymbol temp = left.getRootSymbol();
            if (binary == null) {
                if (temp.getArity() != 2) {return null;}
                binary = temp;
            }
            if (!temp.equals(binary)) {return null;}
            if (right.isVariable()) {return null;}
            temp = ((TRSFunctionApplication)right).getRootSymbol();
            if (!temp.equals(binary)) {return null;}
            TRSTerm t1 = left.getArgument(0);
            if (t1.isVariable()) {
                // potential type P
                TRSTerm t2 = left.getArgument(1);
                if (t2.isVariable()) {return null;}
                TRSTerm sLeft = TRSTerm.createVariable("x");
                while (!t2.isVariable()) {
                    final FunctionSymbol sym = ((TRSFunctionApplication)t2).getRootSymbol();
                    if (sym.getArity() != 1) {return null;}
                    sigmaP.add(sym);
                    sLeft = TRSTerm.createFunctionApplication(sym, new TRSTerm[] {sLeft});
                    t2 = ((TRSFunctionApplication)t2).getArgument(0);
                }
                if (((TRSVariable)t1).getName().equals(((TRSVariable)t2).getName())) {return null;}
                // now in t1 is x and in t2 is y
                final TRSTerm s2 = ((TRSFunctionApplication)right).getArgument(1);
                if (!s2.isVariable()) {return null;}
                if (!((TRSVariable)s2).getName().equals(((TRSVariable)t2).getName())) {return null;}
                TRSTerm s1 = ((TRSFunctionApplication)right).getArgument(0);
                if (s1.isVariable()) {return null;}
                TRSTerm sRight = TRSTerm.createVariable("x");
                while (!s1.isVariable()) {
                    final FunctionSymbol sym = ((TRSFunctionApplication)s1).getRootSymbol();
                    if (sym.getArity() != 1) {return null;}
                    sigmaP.add(sym);
                    sRight = TRSTerm.createFunctionApplication(sym, new TRSTerm[] {sRight});
                    s1 = ((TRSFunctionApplication)s1).getArgument(0);
                }
                if (!((TRSVariable)s1).getName().equals(((TRSVariable)t1).getName())) {return null;}
                srs.add(Rule.create(this.reverse(sLeft, TRSTerm.createVariable("x")),sRight));
            } else {
                // potential type Pprime
                final TRSTerm t2 = left.getArgument(1);
                if (!t2.isVariable()) {return null;}
                final FunctionSymbol sym = ((TRSFunctionApplication)t1).getRootSymbol();
                if (sym.getArity() != 1) {return null;}
                t1 = ((TRSFunctionApplication)t1).getArgument(0);
                if (!t1.isVariable()) {return null;}
                if (((TRSVariable)t1).getName().equals(((TRSVariable)t2).getName())) {return null;}
                // now in t1 is x and in t2 is y
                final TRSTerm s1 = ((TRSFunctionApplication)right).getArgument(0);
                if (!s1.isVariable()) {return null;}
                if (!((TRSVariable)s1).getName().equals(((TRSVariable)t1).getName())) {return null;}
                TRSTerm s2 = ((TRSFunctionApplication)right).getArgument(1);
                if (s2.isVariable()) {return null;}
                if (!((TRSFunctionApplication)s2).getRootSymbol().equals(sym)) {return null;}
                s2 = ((TRSFunctionApplication)s2).getArgument(0);
                if (!s2.isVariable()) {return null;}
                if (!((TRSVariable)s2).getName().equals(((TRSVariable)t2).getName())) {return null;}
                sigmaPprime.add(sym);
            }
        }
        if (!sigmaP.equals(sigmaPprime)) {return null;}
        return QTRSProblem.create(ImmutableCreator.create(srs));
    }

    public QTRSProblem dualZantemaToSRS(final QDPProblem qdp) {
        if (Globals.useAssertions) {
            assert(qdp.getR().isEmpty());
        }
        final Set<Rule> P = qdp.getP();
        if (P.size() < 2) {return null;}
        FunctionSymbol binary = null;
        final Set<FunctionSymbol> sigmaP = new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> sigmaPprime = new LinkedHashSet<FunctionSymbol>();
        final Set<Rule> srs = new LinkedHashSet<Rule>();
        for (final Rule dp : P) {
            final TRSFunctionApplication left = dp.getLeft();
            final TRSTerm right = dp.getRight();
            FunctionSymbol temp = left.getRootSymbol();
            if (binary == null) {
                if (temp.getArity() != 2) {return null;}
                binary = temp;
            }
            if (!temp.equals(binary)) {return null;}
            if (right.isVariable()) {return null;}
            temp = ((TRSFunctionApplication)right).getRootSymbol();
            if (!temp.equals(binary)) {return null;}
            TRSTerm t1 = left.getArgument(1);
            if (t1.isVariable()) {
                // potential type P
                TRSTerm t2 = left.getArgument(0);
                if (t2.isVariable()) {return null;}
                TRSTerm sLeft = TRSTerm.createVariable("x");
                while (!t2.isVariable()) {
                    final FunctionSymbol sym = ((TRSFunctionApplication)t2).getRootSymbol();
                    if (sym.getArity() != 1) {return null;}
                    sigmaP.add(sym);
                    sLeft = TRSTerm.createFunctionApplication(sym, new TRSTerm[] {sLeft});
                    t2 = ((TRSFunctionApplication)t2).getArgument(0);
                }
                if (((TRSVariable)t1).getName().equals(((TRSVariable)t2).getName())) {return null;}
                // now in t1 is x and in t2 is y
                final TRSTerm s2 = ((TRSFunctionApplication)right).getArgument(0);
                if (!s2.isVariable()) {return null;}
                if (!((TRSVariable)s2).getName().equals(((TRSVariable)t2).getName())) {return null;}
                TRSTerm s1 = ((TRSFunctionApplication)right).getArgument(1);
                if (s1.isVariable()) {return null;}
                TRSTerm sRight = TRSTerm.createVariable("x");
                while (!s1.isVariable()) {
                    final FunctionSymbol sym = ((TRSFunctionApplication)s1).getRootSymbol();
                    if (sym.getArity() != 1) {return null;}
                    sigmaP.add(sym);
                    sRight = TRSTerm.createFunctionApplication(sym, new TRSTerm[] {sRight});
                    s1 = ((TRSFunctionApplication)s1).getArgument(0);
                }
                if (!((TRSVariable)s1).getName().equals(((TRSVariable)t1).getName())) {return null;}
                srs.add(Rule.create(this.reverse(sLeft, TRSTerm.createVariable("x")),sRight));
            } else {
                // potential type Pprime
                final TRSTerm t2 = left.getArgument(0);
                if (!t2.isVariable()) {return null;}
                final FunctionSymbol sym = ((TRSFunctionApplication)t1).getRootSymbol();
                if (sym.getArity() != 1) {return null;}
                t1 = ((TRSFunctionApplication)t1).getArgument(0);
                if (!t1.isVariable()) {return null;}
                if (((TRSVariable)t1).getName().equals(((TRSVariable)t2).getName())) {return null;}
                // now in t1 is x and in t2 is y
                final TRSTerm s1 = ((TRSFunctionApplication)right).getArgument(1);
                if (!s1.isVariable()) {return null;}
                if (!((TRSVariable)s1).getName().equals(((TRSVariable)t1).getName())) {return null;}
                TRSTerm s2 = ((TRSFunctionApplication)right).getArgument(0);
                if (s2.isVariable()) {return null;}
                if (!((TRSFunctionApplication)s2).getRootSymbol().equals(sym)) {return null;}
                s2 = ((TRSFunctionApplication)s2).getArgument(0);
                if (!s2.isVariable()) {return null;}
                if (!((TRSVariable)s2).getName().equals(((TRSVariable)t2).getName())) {return null;}
                sigmaPprime.add(sym);
            }
        }
        if (!sigmaP.equals(sigmaPprime)) {return null;}
        return QTRSProblem.create(ImmutableCreator.create(srs));
    }

    private TRSFunctionApplication reverse(TRSTerm left, final TRSVariable x) {
        if (Globals.useAssertions) {
            assert(!left.isVariable());
        }
        TRSTerm t = x;
        while (!left.isVariable()) {
            final TRSFunctionApplication fapp = (TRSFunctionApplication)left;
            if (Globals.useAssertions) {
                assert(fapp.getRootSymbol().getArity() == 1);
            }
            t = TRSTerm.createFunctionApplication(fapp.getRootSymbol(), new TRSTerm[] {t});
            left = fapp.getArgument(0);
        }
        if (Globals.useAssertions) {
            assert(x.equals(left));
        }
        return (TRSFunctionApplication) t;
    }

    private static QTRSProblem plainToSRS(final QDPProblem qdp, final Abortion aborter)
            throws AbortionException {
        // TODO assertion that R and P may only contain syms of arity <= 1
        final ImmutableSet<Rule> r = qdp.getR();
        final ImmutableSet<Rule> p = qdp.getP();
        final Set<Rule> newR = new LinkedHashSet<Rule>(r.size() + p.size());
        newR.addAll(r);
        newR.addAll(p);
        return QTRSProblem.create(ImmutableCreator.create(newR), qdp.getQ().getTerms());
    }

    public class QDPToSRSProof extends QDPProof {

        QDPProblem qdp;
        QTRSProblem srs;
        boolean zantema;

        public QDPToSRSProof(final QDPProblem qdp, final QTRSProblem srs, final boolean zantema) {
            this.qdp = qdp;
            this.srs = srs;
            this.zantema = zantema;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("The finiteness of this DP problem is implied by strong termination of a SRS due to "+o.cite(Citation.UNKNOWN)+".");
            sb.append(o.linebreak());
            return sb.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            if (modus.isPositive()) {
                return CPFTag.DP_PROOF.create(doc, CPFTag.DP_TO_TRS_PROC.create(doc,
                        childrenProofs[0]));
            } else {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive() && !this.zantema;
        }

        @Override
        public String getNonCPFExportableReason(final CPFModus modus) {
            return this.getClass().getCanonicalName() + " only for soundness and non-zantema";
        }

    }

    public static class Arguments {
        public boolean zantema = true; // arbitrary init value
    }

}
