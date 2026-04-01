package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.HaskellProblem.*;

/**
 * @author Stephan Swiderski
 */
public class IrrPatReductionProof extends HaskellProof {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.TerminationProofs");

    public IrrPatReductionProof (){
    }

    public IrrPatReductionProof (HaskellProgram oldHaskellProgram, HaskellProgram newHaskellProgram){
        super(oldHaskellProgram, newHaskellProgram);
        this.name = "IrrPatReduction";
        this.shortName = "IPR";
        this.longName = "IrrPatReduction";
    }

    /**
     * Formats the output string of the proof and returns it.
     */
    @Override
    public String export(Export_Util o) {
        this.startUp();
        this.result.append("IrrPat Reductions:");
        this.result.append(this.exportSets(o,"The variables of the following irrefutable Pattern","are replaced by calls to these functions"));
        return this.result.toString();
    };

    /**
     * Returns a BibTeX citation string for elements of this proof.
     */
    @Override
    public String toBibTeX(){
    // No citations are given.
    return "";
    };
}
