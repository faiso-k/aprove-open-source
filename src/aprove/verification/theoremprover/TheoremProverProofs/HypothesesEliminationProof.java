package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * The proof for hypotheses elimination
 *
 * @author dickmeis
 * @version $Id$
 *
 */

public class HypothesesEliminationProof extends TheoremProverProof {

    private Set<HypothesisPair> removedHpotheses;

    public HypothesesEliminationProof(Set<HypothesisPair> removedHpotheses) {
        this.removedHpotheses = removedHpotheses;

        this.name = "Hypotheses Elimination";
        this.shortName = "Hypotheses Elimination";
        this.longName = "Hypotheses Elimination";
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("The following hypotheses will be ignored " +
                "and are therefore removed from the obligation:"));
        stringBuffer.append(o.linebreak());

        for(Pair<Formula,Set<VariableSymbol>> hypothesis : this.removedHpotheses) {
            stringBuffer.append(o.export(hypothesis));
            stringBuffer.append(o.linebreak());
        }

        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {
        Set<HypothesisPair> hypotheses = new LinkedHashSet<HypothesisPair>();
        for(HypothesisPair hypothesis : this.removedHpotheses) {

            Set<VariableSymbol> variableSymbols = new LinkedHashSet<VariableSymbol>();

            hypotheses.add(new HypothesisPair(hypothesis.x.deepcopy(),variableSymbols));
        }

        return new HypothesesEliminationProof(hypotheses);
    }

}
