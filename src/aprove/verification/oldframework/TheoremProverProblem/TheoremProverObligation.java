/*
 * Created on 07.07.2004
 *
 */
package aprove.verification.oldframework.TheoremProverProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * @author rabe
 * $Id$
 */

public class TheoremProverObligation extends DefaultBasicObligation implements HTML_Able, LaTeX_Able, PLAIN_Able {

    public static final int DEFAULT_DEPTH = 15;
    private static int maxDepth = TheoremProverObligation.DEFAULT_DEPTH;

    protected Formula formula;

    protected Program program;

    protected Map<HypothesisPair, Integer> hypotheses;

    protected Set<Pair<Formula, Set<VariableSymbol>>> inductionHypothesis;

    protected Set<Formula> lemmasUsedSoFar;

    protected boolean resultOfSymbolicEvaluationUnderHypotheses;

    protected HashSet lemmaDirectorConfiguration;

    protected Set<Formula> ancestorFormulas;

    private boolean indirectProof;

    public TheoremProverObligation() {
        super("Formula", "Formula");

        this.hypotheses = new LinkedHashMap<HypothesisPair, Integer>();
        this.lemmasUsedSoFar = new LinkedHashSet<Formula>();
        this.lemmaDirectorConfiguration = new HashSet();
        this.ancestorFormulas = new LinkedHashSet<Formula>();

        this.indirectProof = false;
    }

    /**
     * Constructor creates an obligation which hypothesis set and inductionvariable
     * set is empty
     * @param formula Formula this obligation should be based on
     * @param program Program this obligation should be associated with
     */
    public TheoremProverObligation(final Formula formula, final Program program) {
        super("Formula", "Formula");

        this.resultOfSymbolicEvaluationUnderHypotheses = false;
        this.formula = formula;
        this.program = program;
        this.inductionHypothesis = new LinkedHashSet<Pair<Formula, Set<VariableSymbol>>>();
        this.hypotheses = new LinkedHashMap<HypothesisPair, Integer>();
        this.lemmasUsedSoFar = new LinkedHashSet<Formula>();
        this.lemmaDirectorConfiguration = new HashSet();
        this.ancestorFormulas = new LinkedHashSet<Formula>();

        this.indirectProof = false;
    }

    /**
     * Constructor creates an obligation which hypothesis set and inductionvariable
     * set is empty
     * @param formula Formula this obligation should be based on
     * @param parentObligation the parent obligation to supply common information
     */
    public TheoremProverObligation(final Formula formula, final TheoremProverObligation parentObligation) {
        super("Formula", "Formula");

        this.resultOfSymbolicEvaluationUnderHypotheses = false;
        this.formula = formula;
        this.program = parentObligation.getProgram();
        this.inductionHypothesis =
            new LinkedHashSet<Pair<Formula, Set<VariableSymbol>>>(parentObligation.getInductionHypothesis());
        this.hypotheses = new LinkedHashMap<HypothesisPair, Integer>(parentObligation.getHypotheses());
        this.lemmasUsedSoFar = new LinkedHashSet<Formula>(parentObligation.getLemmasUsedSoFar());
        this.lemmaDirectorConfiguration = new HashSet(parentObligation.getLemmaDirectorConfiguration());
        this.ancestorFormulas = new LinkedHashSet<Formula>(parentObligation.getAncestorFormulas());
        this.ancestorFormulas.add(parentObligation.getFormula());

        this.indirectProof = parentObligation.indirectProof;
    }

    /**
     * Creates an obligation with the given attributes
     * @param formula Formula the obligation should be based on
     * @param program Program the obligation should be associated with
     * @param hypothesis Set of hypothesis to use
     * @param parentObligation the parent obligation to supply common information
     */
    public TheoremProverObligation(final Formula formula, final Program program, final Set<HypothesisPair> hypotheses,
            final TheoremProverObligation parentObligation) {
        super("Formula", "Formula");

        this.resultOfSymbolicEvaluationUnderHypotheses = false;
        this.formula = formula;
        this.program = program;

        this.hypotheses = new LinkedHashMap<HypothesisPair, Integer>();
        for (final HypothesisPair hypothesis : hypotheses) {
            this.hypotheses.put(hypothesis, Integer.valueOf(0));
        }

        this.inductionHypothesis = new LinkedHashSet<Pair<Formula, Set<VariableSymbol>>>(hypotheses);
        this.lemmasUsedSoFar = new LinkedHashSet<Formula>(parentObligation.getLemmasUsedSoFar());
        this.lemmaDirectorConfiguration = new HashSet(parentObligation.getLemmaDirectorConfiguration());
        this.ancestorFormulas = new LinkedHashSet<Formula>(parentObligation.getAncestorFormulas());
        this.ancestorFormulas.add(parentObligation.getFormula());

        this.indirectProof = parentObligation.indirectProof;
    }

    /**
     * Exports the given obligation to a string. Currently this method
     * only calls the toString-Method of the contained formula
     */
    @Override
    public String toString() {
        return this.formula.toString();
    }

    /**
     * Returns a shallowcopy of the given obligation
     */
    public TheoremProverObligation shallowcopy() {

        final TheoremProverObligation theoremProverObligation = new TheoremProverObligation();

        theoremProverObligation.formula = this.formula;
        theoremProverObligation.program = this.program;
        theoremProverObligation.hypotheses = new LinkedHashMap<HypothesisPair, Integer>(this.hypotheses);

        return theoremProverObligation;
    }

    /**
     * Returns a  deepcopy of the given obligation
     */
    @Override
    public TheoremProverObligation deepcopy() {

        TheoremProverObligation deepcopy;

        deepcopy = new TheoremProverObligation();

        deepcopy.formula = this.formula.deepcopy();
        deepcopy.program = this.program.deepercopy();
        deepcopy.hypotheses = new LinkedHashMap<HypothesisPair, Integer>();
        deepcopy.inductionHypothesis = new LinkedHashSet<Pair<Formula, Set<VariableSymbol>>>();

        for (final Map.Entry<HypothesisPair, Integer> hypothesis : this.hypotheses.entrySet()) {

            final Set<VariableSymbol> variableSymbols = new LinkedHashSet<VariableSymbol>();

            for (final VariableSymbol variableSymbol : hypothesis.getKey().y) {
                variableSymbols.add((VariableSymbol) variableSymbol.deepcopy());
            }

            final HypothesisPair copy = new HypothesisPair(hypothesis.getKey().x.deepcopy(), variableSymbols);

            if (this.inductionHypothesis.contains(hypothesis.getKey())) {
                deepcopy.inductionHypothesis.add(copy);
            }

            deepcopy.hypotheses.put(copy, Integer.valueOf(hypothesis.getValue()));
        }

        deepcopy.lemmasUsedSoFar = new LinkedHashSet<Formula>();
        for (final Formula lemma : this.lemmasUsedSoFar) {
            deepcopy.lemmasUsedSoFar.add(lemma.deepcopy());
        }

        deepcopy.ancestorFormulas = new LinkedHashSet<Formula>();
        for (final Formula formula : this.ancestorFormulas) {
            deepcopy.ancestorFormulas.add(formula.deepcopy());
        }

        deepcopy.lemmaDirectorConfiguration = new HashSet(this.lemmaDirectorConfiguration);

        deepcopy.indirectProof = this.indirectProof;

        return deepcopy;
    }

    @Override
    public BasicObligation maybeCopy() {
        return this.deepcopy();
    }

    /**
     * Set the maximal depth for the obligation
     */
    public static void setMaxDepth(final int maxDepth) {
        TheoremProverObligation.maxDepth = maxDepth;
    }

    /**
     * Returns the maximal depth for the obligation tree
     */
    public static int getMaxDepth() {
        return TheoremProverObligation.maxDepth;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.formula == null) ? 0 : this.formula.hashCode());
        result = prime * result + ((this.hypotheses == null) ? 0 : this.hypotheses.hashCode());
        return result;
    }

    /**
     * Returns true if given object is a theorem prover obligation and this
     * obligation is equal to this obligation. Two obligation are equale if
     * their contained formulas, their hypothesis set and their induction
     * variables are equal?
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final TheoremProverObligation other = (TheoremProverObligation) obj;
        if (this.formula == null) {
            if (other.formula != null) {
                return false;
            }
        } else if (!this.formula.equals(other.formula)) {
            return false;
        }
        if (this.hypotheses == null) {
            if (other.hypotheses != null) {
                return false;
            }
        } else if (!this.hypotheses.equals(other.hypotheses)) {
            return false;
        }
        return true;
    }

    @Override
    public String export(final Export_Util o) {

        final StringBuilder stringBuffer = new StringBuilder();

        stringBuffer.append(o.bold("Formula:"));
        stringBuffer.append(o.linebreak());
        if (this.indirectProof) {
            stringBuffer.append(o.export(new NegatedFormulaPair(this.formula, this.formula.getAllVariableSymbols())));
        } else {
            stringBuffer.append(o.export(this.formula));
        }
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.linebreak());
        if (this.hypotheses.isEmpty()) {
            stringBuffer.append(o.bold("There are no hypotheses."));
            stringBuffer.append(o.linebreak());
        } else {

            stringBuffer.append(o.bold("Hypotheses:"));
            stringBuffer.append(o.linebreak());

            for (final Map.Entry<HypothesisPair, Integer> hypothesis : this.hypotheses.entrySet()) {
                stringBuffer.append(o.export(new HypothesisPair(hypothesis.getKey())));
                stringBuffer.append(o.linebreak());
            }

        }

        stringBuffer.append(o.linebreak());

        // needed for nicer output in latex export
        stringBuffer.append(o.paragraph());

        return stringBuffer.toString();
    }

    public Set<AlgebraVariable> getAllVariables() {

        final Set<AlgebraVariable> variables = new LinkedHashSet<AlgebraVariable>();
        variables.addAll(this.formula.getAllVariables());
        for (final Map.Entry<HypothesisPair, Integer> hypothesis : this.hypotheses.entrySet()) {
            variables.addAll(hypothesis.getKey().x.getAllVariables());
        }
        return variables;
    }

    @Override
    public String toLaTeX() {
        return this.export(new LaTeX_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toPLAIN() {
        return this.export(new PLAIN_Util());
    }

    public Formula getFormula() {
        return this.formula;
    }

    public void setFormula(final Formula formula) {
        this.formula = formula;
    }

    public Map<HypothesisPair, Integer> getHypotheses() {
        return new LinkedHashMap<HypothesisPair, Integer>(this.hypotheses);
    }

    public void addHypothesis(final Formula formula, final Set<VariableSymbol> quantifiedVariables) {
        this.hypotheses.put(new HypothesisPair(formula, quantifiedVariables), Integer.valueOf(0));
    }

    public void setHypotheses(final Map<HypothesisPair, Integer> hypotheses) {
        this.hypotheses = hypotheses;
    }

    public Program getProgram() {
        return this.program;
    }

    public void setProgram(final Program program) {
        this.program = program;
    }

    public Set<Formula> getLemmasUsedSoFar() {
        return this.lemmasUsedSoFar;
    }

    public void setLemmasUsedSoFar(final Set<Formula> lemmasUsedSoFar) {
        this.lemmasUsedSoFar = lemmasUsedSoFar;
    }

    public void addUsedLemmas(final Collection<Formula> lemmas) {
        this.lemmasUsedSoFar.addAll(lemmas);
    }

    public boolean isResultOfSymbolicEvaluationUnderHypotheses() {
        return this.resultOfSymbolicEvaluationUnderHypotheses;
    }

    public void setResultOfSymbolicEvaluationUnderHypotheses(final boolean resultOfSymbolicEvaluationUnderHypotheses) {
        this.resultOfSymbolicEvaluationUnderHypotheses = resultOfSymbolicEvaluationUnderHypotheses;
    }

    public void markHypothesesAsUsed(final Collection<HypothesisPair> formulas) {
        for (final HypothesisPair formula : formulas) {
            if (this.hypotheses.containsKey(formula)) {
                this.hypotheses.put(formula, Integer.valueOf(this.hypotheses.get(formula) + 1));
            }
        }
    }

    public Set<HypothesisPair> getHypothesesAsSet() {
        return new LinkedHashSet<HypothesisPair>(this.hypotheses.keySet());
    }

    public Set<HypothesisPair> getAllUsedHypotheses(final int limit) {
        final Set<HypothesisPair> unusedHypotheses = new LinkedHashSet<HypothesisPair>();

        for (final Map.Entry<HypothesisPair, Integer> hypothesis : this.hypotheses.entrySet()) {
            if (hypothesis.getValue() < limit) {
                unusedHypotheses.add(hypothesis.getKey());
            }
        }

        return unusedHypotheses;
    }

    public Set<Pair<Formula, Set<VariableSymbol>>> getInductionHypothesis() {
        return this.inductionHypothesis;
    }

    public void setInductionHypothesis(final Set<Pair<Formula, Set<VariableSymbol>>> inductionHypothesis) {
        this.inductionHypothesis = inductionHypothesis;
    }

    public HashSet getLemmaDirectorConfiguration() {
        return this.lemmaDirectorConfiguration;
    }

    public void setLemmaDirectorConfiguration(final HashSet lemmaDirectorConfiguration) {
        this.lemmaDirectorConfiguration = lemmaDirectorConfiguration;
    }

    public Set<Formula> getAncestorFormulas() {
        return this.ancestorFormulas;
    }

    /**
     * @return true iff we are doing an indirect proof
     */
    public boolean isIndirectProof() {
        return this.indirectProof;
    }

    /**
     * Sets if we are doing an indirect proof
     *
     * @param indirectProof true iff we are doing an indirect proof
     */
    public void setIndirectProof(final boolean indirectProof) {
        this.indirectProof = indirectProof;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new TheoremProverFrameProof(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return null;
    }
}
