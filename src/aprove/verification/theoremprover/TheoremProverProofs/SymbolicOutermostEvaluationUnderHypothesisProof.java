package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TerminationProofs.*;


/**
 * @author dickmeis
 * @version $Id$
 */
public class SymbolicOutermostEvaluationUnderHypothesisProof extends
        TheoremProverProof {

    protected Set<HypothesisPair> hypotheses;

    protected TheoremProverObligation newObligation;

    public SymbolicOutermostEvaluationUnderHypothesisProof() {
    }

    public SymbolicOutermostEvaluationUnderHypothesisProof(
            TheoremProverObligation newObligation,
            Set<HypothesisPair> hypotheses) {

        this.name = "Symbolic outermost evaluation under hypothesis";
        this.longName = "Symbolic outermost evaluation under hypothesis";
        this.shortName = "Symbolic outermost evaluation under hypothesis";

        this.hypotheses = hypotheses;
        this.newObligation = newObligation;
    }

    /*
     * (non-Javadoc)
     *
     * @see aprove.verification.theoremprover.TerminationProofs.Proof#export(aprove.verification.oldframework.Utility.Export_Util)
     */
    @Override
    public String export(Export_Util o) {
        if (Proof.CACHE_VALUES) {
            if (this.result.length() != 0){
                return this.result.toString();
            }
        }
        else {
            this.startUp();
        }

        StringBuffer stringBuffer = new StringBuffer();
        if (this.hypotheses.isEmpty()) {
            stringBuffer.append(o.bold("Could be reduce to "
                    + o.export(FormulaTruthValue.TRUE)
                    + " due to an inconsistent hypotheses set."));
        }
        else if (this.newObligation.getFormula().equals(FormulaTruthValue.TRUE)) {
            stringBuffer.append(
                    o.bold("Could be shown using symbolic evaluation under hypothesis, by using the following hypotheses:"));
            stringBuffer.append(o.paragraph());
        }
        else if (this.newObligation.getFormula().equals(FormulaTruthValue.FALSE)) {
            stringBuffer.append(
                    o.bold("Could be disproved using symbolic evaluation under hypothesis, by using the following hypotheses:"));
            stringBuffer.append(o.paragraph());
        }
        else {
            stringBuffer.append(
                    o.bold("Could be reduced by symbolic evaluation under hypothesis to:"));
            stringBuffer.append(o.linebreak());
            stringBuffer.append(o.export(this.newObligation.getFormula()));
            stringBuffer.append(o.paragraph());
            stringBuffer.append(o.bold("By using the following hypotheses:"));
            stringBuffer.append(o.linebreak());
        }

        for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypotheses) {
            stringBuffer.append(o.export(hypothesis));
            stringBuffer.append(o.linebreak());
        }

        return stringBuffer.toString();
    }

    public TheoremProverObligation getNewObligation() {
        return this.newObligation;
    }

    public void setNewObligation(TheoremProverObligation newObligation) {
        this.newObligation = newObligation;
    }

    public Set<HypothesisPair> getHypotheses() {
        return this.hypotheses;
    }

    public void setHypotheses(Set<HypothesisPair> hypotheses) {
        this.hypotheses = hypotheses;
    }

    @Override
    public Proof deepcopy() {
        Set<HypothesisPair> hypotheses = new LinkedHashSet<HypothesisPair>();
        for (HypothesisPair hypothesis : this.hypotheses) {

            Set<VariableSymbol> variableSymbols = new LinkedHashSet<VariableSymbol>();

            hypotheses.add(new HypothesisPair(hypothesis.x.deepcopy(), variableSymbols));
        }

        return new SymbolicOutermostEvaluationUnderHypothesisProof(
                this.newObligation.deepcopy(), hypotheses);
    }
}
