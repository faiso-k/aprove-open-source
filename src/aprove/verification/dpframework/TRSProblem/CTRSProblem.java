/*
 * Created on 11.04.2005
 */
package aprove.verification.dpframework.TRSProblem;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Output.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

public final class CTRSProblem extends DefaultBasicObligation implements HTML_Able, ExternUsable {

    private final ImmutableSet<Rule> R;
    private final ImmutableSet<ConditionalRule> C;
    private volatile ImmutableSet<FunctionSymbol> signature;

    // cached / calculated values
    private final int hashCode;

    private static boolean checkConstructorArgs(final ImmutableSet<Rule> R, final ImmutableSet<ConditionalRule> C) {
        return R != null && C != null;
    }

    /**
     * creates a CTRS problem.
     * @param R the simple rules
     * @param C the conditional rules
     */
    private CTRSProblem(final ImmutableSet<Rule> R, final ImmutableSet<ConditionalRule> C) {
        super("CTRS", "Conditional TRS");
        assert(CTRSProblem.checkConstructorArgs(R, C));
        this.R = R;
        this.C = C;
        this.hashCode = this.R.hashCode()*849033+this.C.hashCode()*84903+8490213;
        this.signature = null;
    }

    /**
     * creates a new CTRS-Problem
     * @param R the simple rules
     * @param C the conditional rules
     */
    public static CTRSProblem create(final ImmutableSet<Rule> R,
        final ImmutableSet<ConditionalRule> C) {
        return new CTRSProblem(R, C);
    }

    @Override
    public boolean equals(final Object oth) {
        if (this == oth) {
            return true;
        }

        if (oth == null) {
            return false;
        }

        if (oth.getClass() != this.getClass()) {
            return false;
        }

        final CTRSProblem other = (CTRSProblem) oth;
        if (!this.R.equals(other.R)) {
            return false;
        }

        return this.C.equals(other.C);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }


    public ImmutableSet<Rule> getR() {
        return this.R;
    }

    public ImmutableSet<ConditionalRule> getC() {
        return this.C;
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuffer s = new StringBuffer();
        s.append(o.export("Conditional term rewrite system:"));
        s.append(o.cond_linebreak());
        if (this.R.isEmpty()) {
            s.append("The TRS R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.R, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        if (this.C.isEmpty()) {
            s.append("The conditional TRS C is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The conditional TRS C consists of the following conditional rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.C, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        return s.toString();
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        final Element rules = CPFTag.RULES.create(doc);
        for (final Rule rule : this.R) {
            rules.appendChild(rule.toCPF(doc, xmlMetaData));
        }
        for (final ConditionalRule rule : this.C) {
            rules.appendChild(rule.toCPF(doc, xmlMetaData));
        }
        return CPFTag.CTRS_INPUT.create(doc, rules);
    }

    @Override
    public String toExternString() {
        final TRSGenerator trsGen = new TRSGenerator();
        trsGen.writeRules(this.R);
        trsGen.writeConditionalRules(this.C);
        return trsGen.getTRSString(false, null);
    }

    @Override
    public String externName() {
        return "trs";
    }


    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    /**
     * Get a FreshNameGenerator to build function symbols that are guaranteed not to
     * conflict with the signature of this CTRS.
     * @return A FreshNameGenerator where all names of the signature are marked as used.
     */
    public FreshNameGenerator getFreshNameGenerator() {
        final Set<String> used = new LinkedHashSet<String>();
        for (final FunctionSymbol f : CollectionUtils.getFunctionSymbols(this.R)) {
            used.add(f.getName());
        }
        for (final FunctionSymbol f : CollectionUtils.getFunctionSymbols(this.C)) {
            used.add(f.getName());
        }
        return new FreshNameGenerator(used, FreshNameGenerator.PROLOG_VARS);
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Quasi decreasingness");
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        if (this.signature == null) {
            synchronized (this) {
                if (this.signature == null) {
                    this.computeSignatures();
                }
            }
        }
        return this.signature;
    }

    private void computeSignatures() {
        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.R);
        this.signature = ImmutableCreator.create(signature);
        // create a copy
        signature = new LinkedHashSet<FunctionSymbol>(signature);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.C));
        this.signature = ImmutableCreator.create(signature);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "ctrs";
    }
}
