package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.HaskellProblem.*;

/**
 * @author Stephan Swiderski
 */
public class NumReductionProof extends HaskellProof {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.TerminationProofs");

    public NumReductionProof(){
    }

    public NumReductionProof (HaskellProgram oldHaskellProgram, HaskellProgram newHaskellProgram){
    super(oldHaskellProgram, newHaskellProgram);
    this.name = "NumReduction";
    this.shortName = "NumRed";
    this.longName = "NumReduction";
    }

    /**
     * Formats the output string of the proof and returns it.
     */
    @Override
    public String export(Export_Util o) {
        this.startUp();
        this.result.append("Num Reduction:");
        this.result.append("All numbers are transformed to their corresponding representation with Succ, Pred and Zero.");
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
