package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.HaskellProblem.*;

/**
 * @author Stephan Swiderski
 */
public class IfReductionProof extends HaskellProof {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.TerminationProofs");

    public IfReductionProof(){
    }

    public IfReductionProof (HaskellProgram oldHaskellProgram, HaskellProgram newHaskellProgram){
    super(oldHaskellProgram, newHaskellProgram);
    this.name = "IfReduction";
    this.shortName = "IFR";
    this.longName = "IfReduction";
    }

    /**
     * Formats the output string of the proof and returns it.
     */
    @Override
    public String export(Export_Util o) {
        this.startUp();
        this.result.append("If Reductions:");
        this.result.append(this.export(o,"The following If expression","is transformed to"));
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
