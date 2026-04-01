package aprove.verification.dpframework.TRSProblem;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.xml.*;
import immutables.*;

/**
 * a OTRS is a TRS where outermost termination has to be proven
 * @author thiemann
 */
public class OTRSProblem extends DefaultBasicObligation {

    // real values
    private final ImmutableSet<FunctionSymbol> signature;

    // changed by Sebastian Weise (GeneralizedRules !)
    private final ImmutableSet<? extends GeneralizedRule> R;

    private OTRSProblem(final ImmutableSet<? extends GeneralizedRule> R) {
        super("OTRS", "OTRS");
        this.R = R;
        this.signature =
            ImmutableCreator.create(CollectionUtils.getFunctionSymbols(this.R));
    }

    /**
     * creates a new OTRS
     * @param R
     * @return
     */
    public static OTRSProblem create(final Set<? extends GeneralizedRule> R) {
        return new OTRSProblem(ImmutableCreator.create(R));
    }

    public ImmutableSet<? extends GeneralizedRule> getR() {
        return this.R;
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("Term rewrite system R:"));
        s.append(o.cond_linebreak());
        if (this.R.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.R, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        s.append(o.paragraph() + "Outermost Strategy." + o.linebreak());

        return s.toString();
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Outermost Termination");
    }

    /*
    public String toExternString() {
        TRSGenerator trsGen =  new TRSGenerator();
        trsGen.writeGeneralizedRules(this.R);
        return trsGen.getTRSString(this.innermost,null);
    }

    public String externName() {
        return "trs";
    }
     */

    public ImmutableSet<FunctionSymbol> getSignature() {
        return this.signature;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * checks if R is quasi left-linear<br>
     * i.e. every non-linear lhs of a rule in R is an instance of a linear lhs
     * from R
     * @return true, if R is quasi left-linear
     */
    public boolean isQuasiLeftLinear() {
        final Set<TRSFunctionApplication> setLhs = CollectionUtils.getLeftHandSides(this.R);
        final Set<TRSFunctionApplication> linearLhs = new HashSet<TRSFunctionApplication>();
        final Set<TRSFunctionApplication> nonlinearLhs =
            new HashSet<TRSFunctionApplication>();
        for (final TRSFunctionApplication lhs : setLhs) {
            if (lhs.isLinear()) {
                linearLhs.add(lhs);
            } else {
                nonlinearLhs.add(lhs);
            }
        }

        for (final TRSFunctionApplication nonlinLhs : nonlinearLhs) {
            boolean foundInstance = false;
            // is instance of a linear lhs?
            for (final TRSFunctionApplication lin : linearLhs) {
                final TRSSubstitution mgu = nonlinLhs.getMGU(lin);
                if (mgu != null && !mgu.isEmpty()) {
                    foundInstance = true;
                    break;
                }
            }
            if (!foundInstance) {
                return false;
            }
        }

        return true;
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        return CPFTag.TRS_INPUT.create(
            doc,
            CPFTag.trs(doc, xmlMetaData, this.getR()),
            CPFTag.STRATEGY.create(doc, CPFTag.OUTERMOST.create(doc)));
    }

    @Override
    public Element getCPFAssumption(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final CPFModus modus,
        final TruthValue tv)
    {
        if (modus.isPositive()) {
            return CPFTag.TRS_TERMINATION_PROOF.create(
                doc,
                CPFTag.TERMINATION_ASSUMPTION.create(doc, this.getCPFInput(doc, xmlMetaData, tv)));
        } else {
            return CPFTag.TRS_NONTERMINATION_PROOF.create(
                doc,
                CPFTag.NONTERMINATION_ASSUMPTION.create(doc, this.getCPFInput(doc, xmlMetaData, tv)));
        }
    }

    @Override
    public boolean offersCertifiableTechniques() {
        return true;
    }


    /**
    * {@inheritDoc}
    */
    @Override
    public String getStrategyName() {
        return "otrs";
    }
}
