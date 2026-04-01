package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.HaskellProblem.*;

/**
 * @author Stephan Swiderski
 */
public class LetReductionProof extends HaskellProof {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.TerminationProofs");

    public LetReductionProof(){
    }

    public LetReductionProof (HaskellProgram oldHaskellProgram, HaskellProgram newHaskellProgram){
        super(oldHaskellProgram, newHaskellProgram);
        this.name = "LetReduction";
        this.shortName = "LetRed";
        this.longName = "LetReduction";
    }

    /**
     * Formats the output string of the proof and returns it.
     */
    @Override
    public String export(Export_Util o) {
        this.startUp();
        this.result.append("Let/Where Reductions:");
        this.result.append(this.exportSets(o,"The bindings of the following Let/Where expression","are unpacked to the following functions on top level"));
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
