package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TerminationProofs.*;
import aprove.verification.theoremprover.TheoremProverProcedures.Induction.*;

public class InductionByAlgorithmCoverSetProof extends TheoremProverProof {

    protected Set<TheoremProverObligation> inductionCases;

    protected List<Pair<AlgebraTerm,Position>> termsWithPosition;

    protected InductionScheme inductionScheme;

    public InductionByAlgorithmCoverSetProof(
            Set<TheoremProverObligation> inductionCases,
            List<Pair<AlgebraTerm,Position>> termsWithPositions,
            InductionScheme inductionScheme) {

        // init object's variables
        this.shortName  ="Induction by algorithm with cover set";
        this.longName   ="Induction by algorithm with cover set";

        this.termsWithPosition = termsWithPositions;

        this.inductionCases = inductionCases;

        this.inductionScheme = inductionScheme;
    }

    /* (non-Javadoc)
     * @see aprove.verification.theoremprover.TerminationProofs.Proof#export(aprove.verification.oldframework.Utility.Export_Util)
     */
    @Override
    public String export(Export_Util o) {

        if (Proof.CACHE_VALUES) {
                if (this.result.length() != 0) {
                    return this.result.toString();
                }
        }
        else {
            this.startUp();
        }

        StringBuilder returnValue = new StringBuilder();

        returnValue.append(o.bold("Induction by algorithm with cover sets:"));
        returnValue.append(o.paragraph());

        for (Pair<AlgebraTerm,Position> p : this.termsWithPosition) {
            returnValue.append("The induction term at position " + p.y + " is " + p.x.export(o));
            returnValue.append(o.newline());
        }

        returnValue.append("The induction scheme is:\n");
        returnValue.append(this.inductionScheme.export(o));

        returnValue.append(o.paragraph());

          int index=1;
        for(TheoremProverObligation theoremProverObligation : this.inductionCases) {
            returnValue.append(o.bold(index+". induction case:"));
              returnValue.append(o.linebreak());
              returnValue.append(o.indent(o.export(theoremProverObligation)));
            returnValue.append(o.linebreak());
              index++;
         }

        return returnValue.toString();
    }

    public String toBibTeX() {
        return "";
    }

    public Set<TheoremProverObligation> getInductionCases() {
        return this.inductionCases;
    }

    public void setInductionCases(Set<TheoremProverObligation> inductionCases) {
        this.inductionCases = inductionCases;
    }

    @Override
    public Proof deepcopy() {

        Set<TheoremProverObligation> newInductionCases = new LinkedHashSet<TheoremProverObligation>(this.inductionCases.size());
        for(TheoremProverObligation theoremProverObligation : this.inductionCases) {
            newInductionCases.add(theoremProverObligation.deepcopy());
        }

        List<Pair<AlgebraTerm,Position>> newPairs = new ArrayList<Pair<AlgebraTerm,Position>>(this.termsWithPosition.size());
        for (Pair<AlgebraTerm,Position> p : this.termsWithPosition) {
            Pair<AlgebraTerm,Position> newPair = new Pair<AlgebraTerm,Position>(
                    p.x.deepcopy(), p.y.deepcopy());
            newPairs.add(newPair);
        }

        InductionScheme newInductionScheme = this.inductionScheme.deepcopy();


        return new InductionByAlgorithmCoverSetProof(
                newInductionCases,
                newPairs,
                newInductionScheme);
    }

    /**
     * @return the inductionScheme
     */
    public InductionScheme getInductionScheme() {
        return this.inductionScheme;
    }

    /**
     * Thegenerated induction scheme.
     *
     * @param inductionScheme the inductionScheme to set
     */
    public void setInductionScheme(InductionScheme inductionScheme) {
        this.inductionScheme = inductionScheme;
    }
}
