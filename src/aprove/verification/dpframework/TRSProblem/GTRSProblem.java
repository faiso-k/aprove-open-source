package aprove.verification.dpframework.TRSProblem;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Output.*;
import aprove.xml.*;
import immutables.*;

/**
 * a GTRS is a generalized TRS where right-hand side may contain
 * arbitrary fresh variables.
 * @author thiemann
 *
 */
public class GTRSProblem extends DefaultBasicObligation implements XMLObligationExportable {

    // real values

    private final ImmutableSet<GeneralizedRule> R;
    private final boolean innermost;


    private GTRSProblem(final ImmutableSet<GeneralizedRule> R, final boolean innermost) {
        super("GTRS", "GTRS");
        this.R = R;
        this.innermost = innermost;
    }

    /**
     * creates a new CSR provided that all function symbols occurring in R are also present
     * in the replacement map. If some entry is missing, a runtime exception is thrown
     * @param R
     * @param replacementMap
     * @param innermost
     * @return
     */
    public static GTRSProblem create(final Set<GeneralizedRule> R, final boolean innermost) {
        return new GTRSProblem(ImmutableCreator.create(R), innermost);
    }

    public ImmutableSet<GeneralizedRule> getR() {
        return this.R;
    }


    public boolean getInnermost() {
        return this.innermost;
    }


    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("Generalized rewrite system (where rules with free variables on rhs are allowed):"));
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

        if (this.innermost) {
            s.append(o.paragraph()+"Innermost Strategy."+o.linebreak());
        }

        return s.toString();
    }

    public String toExternString() {
        final TRSGenerator trsGen =  new TRSGenerator();
        trsGen.writeGeneralizedRules(this.R);
        return trsGen.getTRSString(this.innermost,null);
    }

    public String externName() {
        return "trs";
    }


    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.GTRS_OBL.createElement(doc);
        final Element f = XMLTag.GTRS.createElement(doc);

        final Element trs = XMLTag.TRS.createElement(doc);
        CollectionUtils.addChildren(this.R, trs, doc, xmlMetaData);
        f.appendChild(trs);

        if (this.innermost) {
            f.appendChild(XMLTag.INNERMOST.createElement(doc));
        }

        e.appendChild(f);
        return e;
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        final Element trsInput = CPFTag.TRS_INPUT.create(doc, CPFTag.trs(doc, xmlMetaData, this.getR()));

        if (this.innermost) {
            trsInput.appendChild(CPFTag.STRATEGY.create(doc,
                    CPFTag.INNERMOST.create(doc)));
        }
        return trsInput;
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



    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this,
                (this.getInnermost() ? "Innermost " : "") + "Termination");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "gtrs";
    }
}
