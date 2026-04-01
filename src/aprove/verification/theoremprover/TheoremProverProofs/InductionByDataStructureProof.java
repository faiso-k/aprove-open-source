/*
 * Created on 18.08.2004
 *
 */
package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * @author rabe
 *

 */
public class InductionByDataStructureProof extends TheoremProverProof {

    protected Set<TheoremProverObligation> baseCases;

    protected Set<TheoremProverObligation> stepCases;

    protected String dataStructure;

    public InductionByDataStructureProof() {
    }

    public InductionByDataStructureProof(Set<TheoremProverObligation> baseCases, Set<TheoremProverObligation> stepCases, String dataStructure ) {

        this.shortName = "Induction by data structure";
        this.longName  = "Induction by data structure";
        this.baseCases         = baseCases;
        this.stepCases         = stepCases;
        this.dataStructure     = dataStructure;
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

        returnValue.append(o.bold("Induction by data structure "+ o.italic(this.dataStructure)+" generates the following cases:"));
        returnValue.append(o.newline());
        returnValue.append(o.paragraph());


        for(TheoremProverObligation theoremProverObligation : this.baseCases) {
            int index=1;
            returnValue.append(o.bold(index+". Base Case:"));
            returnValue.append(o.linebreak());
            returnValue.append(o.indent(o.export(theoremProverObligation)));
            returnValue.append(o.paragraph());
            index++;
        }

        for(TheoremProverObligation theoremProverObligation : this.stepCases) {
            int index = 1;
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

    public String getDataStructure() {
        return this.dataStructure;
    }

    public void setDataStructure(String dataStructure) {
        this.dataStructure = dataStructure;
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
        return new InductionByDataStructureProof(baseCases,stepCases, this.dataStructure);
    }

}
