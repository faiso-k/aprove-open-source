package aprove.verification.dpframework.Utility.NonLoop.structures.proofed;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.equivalence.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.intantiating.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
import aprove.xml.*;
import immutables.*;

/**
 * A ProofedRule consists of:
 * <ul>
 * <li>a {@link PatternRule}</li>
 * <li>a {@link ImmutableSet} R</li>
 * <li>a {@link ImmutableSet} P</li>
 * <li>a flag to indicate whether there was a "P-step" or not: <tt>hasPStep</tt>
 * </li>
 * <li>a flag to indicate whether the full proof should be exported or not</li>
 * </ul>
 *
 * @author Tim Enger
 */

public abstract class ProofedRule
    implements
        Exportable,
        IExportableProof,
        XMLObligationExportable,
        Immutable,
        CPFAdditional
{

    /**
     * Underlying PatternRule
     */
    private final PatternRule pRule;

    /**
     * Underlying set R
     */
    private final ImmutableSet<Rule> setR;

    /**
     * Underlying set R
     */
    private final ImmutableSet<Rule> setP;

    /**
     * Was there a P-step before?
     */
    private final boolean hasPStep;

    /**
     * full proof export?
     */
    private boolean showRule;

    /**
     * cached hashcode
     */
    private final int hashCode;

    /**
     * Constructor
     *
     * @param pRuleArg
     *            The {@link PatternRule} to be used.
     * @param setRArg
     *            The {@link ImmutableSet} R.
     * @param setPArg
     *            The {@link ImmutableSet} P.
     * @param hasPStepArg
     *            <tt>True</tt> if the was a "P-Step" before.
     */
    public ProofedRule(final PatternRule pRuleArg, final ImmutableSet<Rule> setRArg, final ImmutableSet<Rule> setPArg,
            final boolean hasPStepArg) {
        this.pRule = pRuleArg;
        this.setR = setRArg;
        this.setP = setPArg;
        this.hasPStep = hasPStepArg;
        this.showRule = false;

        this.hashCode = 17 * pRuleArg.hashCode() + 23;
    }

    /**
     * Constructor
     *
     * @param lhs
     *            The {@link PatternTerm} lhs.
     * @param rhs
     *            The {@link PatternTerm} rhs.
     * @param r
     *            The {@link ImmutableSet} R.
     * @param p
     *            The {@link ImmutableSet} P.
     * @param hasPStepArg
     *            <tt>True</tt> if the was a "P-Step" before.
     */
    public ProofedRule(final PatternTerm lhs, final PatternTerm rhs, final ImmutableSet<Rule> r,
            final ImmutableSet<Rule> p, final boolean hasPStepArg) {
        this(new PatternRule(lhs, rhs), r, p, hasPStepArg);
    }

    /**
     * Rename.
     *
     * @param used
     *            Avoid these {@link TRSVariable} variables in the renaming.
     * @return THe renamed rule.
     */
    public ProofedRule rename(final Set<TRSVariable> used) {
        PatternRule pr = this.getPatternRule();
        PatternTerm lhs = pr.getLhs();
        PatternTerm rhs = pr.getRhs();

        final Set<TRSVariable> forbidden = new LinkedHashSet<>(used);

        final TRSSubstitution drL = lhs.getDomainRenaming(lhs.getDomainVariables(), forbidden);

        final TRSSubstitution drR = rhs.getDomainRenaming(rhs.getDomainVariables(), forbidden);

        ProofedRule temp = Equivalence.createDomainRenaming(this, drL, drR);

        // let the freshvargen know, that we used these variables, too
        forbidden.addAll(drL.getVariablesInCodomain());
        forbidden.addAll(drR.getVariablesInCodomain());
        final FreshNameGenerator gen = new FreshNameGenerator(forbidden, new PrefixNameGenerator("x"));

        pr = temp.getPatternRule();
        lhs = pr.getLhs();
        rhs = pr.getRhs();

        final Set<TRSVariable> allVars = pr.getAllVariables();
        allVars.removeAll(lhs.getDomainVariables());
        allVars.removeAll(rhs.getDomainVariables());

        final Map<TRSVariable, TRSTerm> rhoMap = new LinkedHashMap<>();

        for (final TRSVariable v : allVars) {
            rhoMap.put(v, TRSTerm.createVariable(gen.getFreshName(v.getName(), false)));
        }

        temp = Instantiation.create(temp, TRSSubstitution.create(ImmutableCreator.create(rhoMap)));

        temp = Equivalence.createRemoveAllIrrelevant(temp);

        assert temp != null;

        return temp;
    }

    /**
     * <p>
     * Renames all variables into standard representation.
     * </p>
     * <p>
     * The standard representation for the lhs. I.e., the variable prefixes
     * <ul>
     * <li>"zl": are used for pattern variables of the lhs</li>
     * <li>"zr": are used for pattern variables of the rhs</li>
     * <li>"x": are used for variables</li>
     * </ul>
     * are used.
     * </p>
     *
     * @return The standard representation for the lhs.
     */
    public ProofedRule getStandardLeft() {
        return this.getStandard("zl", "zr", "x");
    }

    /**
     * <p>
     * Renames all variables into standard representation.
     * </p>
     * <p>
     * The standard representation for the lhs. I.e., the variable prefixes
     * <ul>
     * <li>"zs": are used for pattern variables of the lhs</li>
     * <li>"zt": are used for pattern variables of the rhs</li>
     * <li>"y": are used for variables</li>
     * </ul>
     * are used.
     * </p>
     *
     * @return The standard representation for the rhs.
     */
    public ProofedRule getStandardRight() {
        return this.getStandard("zs", "zt", "y");
    }

    /**
     * Compute the standard representation (rename variables) according to the
     * given prefixes.
     *
     * @param dvL
     *            The prefix for pattern variables of the lhs.
     * @param dvR
     *            The prefix for pattern variables of the rhs.
     * @param vars
     *            The prefix for variables.
     * @return The standard representation w.r.t. to the given renaming.
     */
    private ProofedRule getStandard(final String dvL, final String dvR, final String vars) {

        PatternTerm lhs = this.pRule.getLhs();
        PatternTerm rhs = this.pRule.getRhs();

        final FreshNameGenerator dvLGen = new FreshNameGenerator(lhs.getAllVariables(), new PrefixNameGenerator(dvL));
        final FreshNameGenerator dvRGen = new FreshNameGenerator(rhs.getAllVariables(), new PrefixNameGenerator(dvR));

        // generate mapping for domain vars
        Set<TRSVariable> dVarsL = lhs.getDomainVariables();
        final Map<TRSVariable, TRSVariable> mapL = new LinkedHashMap<>();
        for (final TRSVariable x : dVarsL) {
            mapL.put(x, TRSTerm.createVariable(dvLGen.getFreshName("l", false)));
        }
        final TRSSubstitution drL = lhs.getDomainRenaming(dVarsL, mapL, dVarsL);

        // generate mapping for r
        Set<TRSVariable> dVarsR = rhs.getDomainVariables();
        final Map<TRSVariable, TRSVariable> mapR = new LinkedHashMap<>();
        for (final TRSVariable x : dVarsR) {
            mapR.put(x, TRSTerm.createVariable(dvRGen.getFreshName("r", false)));
        }
        final TRSSubstitution drR = rhs.getDomainRenaming(dVarsR, mapR, dVarsR);

        ProofedRule result = Equivalence.createDomainRenaming(this, drL, drR);

        // generate mapping for non-domain vars

        final PatternRule domainRenamed = result.getPatternRule();

        lhs = domainRenamed.getLhs();
        rhs = domainRenamed.getRhs();

        dVarsL = lhs.getDomainVariables();
        dVarsR = rhs.getDomainVariables();

        final Set<TRSVariable> forbidden = new LinkedHashSet<>(dVarsL);
        forbidden.addAll(dVarsR);

        final FreshNameGenerator varsGen = new FreshNameGenerator(forbidden, new PrefixNameGenerator(vars));

        final Map<TRSVariable, TRSVariable> instMap = new LinkedHashMap<>();
        for (final TRSVariable x : lhs.getNonDomainVariables()) {
            instMap.put(x, TRSTerm.createVariable(varsGen.getFreshName(x.getName(), true)));
        }
        final TRSSubstitution instantiation = TRSSubstitution.create(ImmutableCreator.create(instMap));

        result = Instantiation.create(result, instantiation);

        return result;
    }

    /**
     * @return The underlying {@link PatternRule}.
     */
    public PatternRule getPatternRule() {
        return this.pRule;
    }

    /**
     * @return The underlying {@link ImmutableSet R}.
     */
    public ImmutableSet<Rule> getR() {
        return this.setR;
    }

    /**
     * @return The underlying {@link ImmutableSet P}.
     */
    public ImmutableSet<Rule> getP() {
        return this.setP;
    }

    /**
     * @return <tt>True</tt> if the rule has a "P-step", otherwise
     *         <tt>false</tt>.
     */
    public boolean hasPStep() {
        return this.hasPStep;
    }
    
    /**
     * @return The number of proof steps it took to get to this point.
     */
    public abstract int getProofStepCount();
    
    /**
     * @return The rewrite sequence starting in lhs.instance(1) to the term that leads to non-termination.
     */
    public abstract ImmutableList<Pair<Position,Rule>> reconstructSequence();

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object o) {
        if (this == o) {
            return true;
        }

        if (o == null) {
            return false;
        }

        if (o.hashCode() == this.hashCode) {
            if (o instanceof ProofedRule) {
                return this.pRule.equals(((ProofedRule) o).getPatternRule());
            }
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return this.hashCode;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.pRule.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String export(final Export_Util eu) {
        return this.getPatternRule().export(eu);
    }

    /**
     * Method to recursively export the proof of this rule, including the export
     * of parents.
     *
     * @param eu
     *            THe {@link Export_Util} used.
     * @param indent
     *            The current indentation.
     * @param addIndent
     *            The indentation to add in the next iteration.
     * @param firstIntermediate
     *            Flag to indicate whether this is the first intermediate step
     *            (mainly to allow to not exporting the full proof).
     * @param fullProof
     *            Flag to indicate whether the full proof should be exported, or
     *            intermediate steps should be shown.
     * @return The proof.
     */
    public String export(final Export_Util eu,
        final String indent,
        final String addIndent,
        final boolean firstIntermediate,
        final boolean fullProof) {

        final StringBuilder sb = new StringBuilder();
        String newIndent = indent;
        boolean inter = firstIntermediate;

        if (fullProof || this.isShowRule()) {
            // full proof export
            sb.append(eu.linebreak());
            sb.append(indent);
            sb.append(this.export(eu));
            sb.append(eu.linebreak());

            newIndent += addIndent;
            sb.append(newIndent);
            sb.append("by ");
            sb.append(this.exportProof(eu));
            inter = true;
        } else {
            // smallish proof for intermediate steps
            if (firstIntermediate) {
                sb.append(eu.linebreak());
                sb.append(indent);
                sb.append("intermediate steps: ");
            } else {
                sb.append(" - ");
            }
            sb.append(this.exportProofShort(eu));
            inter = false;
        }

        sb.append(this.exportParents(eu, newIndent, addIndent, inter, fullProof));

        return sb.toString();
    }

    /**
     * Export only your own parents.<br>
     * THis method is to encapsulate the number of and the way of exporting
     * parents. This means, only the proof itself knows its components and
     * parents and this can change at any time.
     *
     * @param eu
     *            THe {@link Export_Util} used.
     * @param indent
     *            The current indentation.
     * @param addIndent
     *            The indentation to add in the next iteration.
     * @param firstIntermediate
     *            Flag to indicate whether this is the first intermediate step
     *            (mainly to allow to not exporting the full proof).
     * @param fullProof
     *            Flag to indicate whether the full proof should be exported, or
     *            intermediate steps should be shown.
     * @return The proof.
     */
    public abstract String exportParents(final Export_Util eu,
        final String indent,
        final String addIndent,
        final boolean firstIntermediate,
        final boolean fullProof);

    /**
     * @return If the flag "show rule" is set.
     */
    public boolean isShowRule() {
        return this.showRule;
    }

    /**
     * Set the "show rule" flag.
     */
    public void setShowRule() {
        this.showRule = true;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return CPFTag.notYetImplemented(doc, this);
    }

}
