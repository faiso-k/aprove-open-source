/*
 * Created on 24.08.2004
 *
 */
package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * @author rabe
 */
public class InductionByAlgorithmProof extends TheoremProverProof {

    protected Set<TheoremProverObligation> baseCases;

    protected Set<TheoremProverObligation> stepCases;

    protected String algorithm;

    public InductionByAlgorithmProof() {
    }

    public InductionByAlgorithmProof( Set<TheoremProverObligation> baseCases, Set<TheoremProverObligation> stepCases, String algorithm ) {

        // init object's variables
        this.shortName    ="Induction by algorithm";
        this.longName    ="Induction by algorithm";

        this.baseCases    = baseCases;
        this.stepCases    = stepCases;
        this.algorithm    = algorithm;

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
        } else {
            this.startUp();
        }

          StringBuffer returnValue = new StringBuffer();

          returnValue.append(o.bold("Induction by algorithm "+o.italic(this.algorithm)+" generates the following cases:"));
          returnValue.append(o.paragraph());

          int index=1;
        for(TheoremProverObligation theoremProverObligation : this.baseCases) {
            returnValue.append(o.bold(index+". Base Case:"));
              returnValue.append(o.linebreak());
              returnValue.append(o.indent(o.export(theoremProverObligation)));
              returnValue.append(o.paragraph());
              index++;
         }

         index = 1;
         for(TheoremProverObligation theoremProverObligation : this.stepCases) {
              returnValue.append(o.bold(index+". Step Case:"));
              returnValue.append(o.linebreak());
              returnValue.append(o.indent(o.export(theoremProverObligation)));
              returnValue.append(o.paragraph());
              index++;
         }

          return returnValue.toString();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Utility.BibTeX_Able#toBibTeX()
     */
    public String toBibTeX() {
        return "";
    }

    public Set<TheoremProverObligation> getBaseCases() {
        return this.baseCases;
    }

    public void setBaseCases(Set<TheoremProverObligation> baseCases) {
        this.baseCases = baseCases;
    }

    public Set<TheoremProverObligation> getStepCases() {
        return this.stepCases;
    }

    public void setStepCases(Set<TheoremProverObligation> stepCases) {
        this.stepCases = stepCases;
    }

    public String getAlgorithm() {
        return this.algorithm;
    }

    public void setAlgorithm(String algorithm) {
        this.algorithm = algorithm;
    }

    @Override
    public Proof deepcopy() {

        Set<TheoremProverObligation> baseCases = new LinkedHashSet<TheoremProverObligation>();
        for(TheoremProverObligation theoremProverObligation : this.baseCases) {
            baseCases.add(theoremProverObligation.deepcopy());
        }

        Set<TheoremProverObligation> stepCases = new LinkedHashSet<TheoremProverObligation>();
        for(TheoremProverObligation theoremProverObligation : this.stepCases) {
            stepCases.add(theoremProverObligation.deepcopy());
        }
        return new InductionByAlgorithmProof(baseCases,stepCases, this.algorithm);
    }


}
