package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * @author Stephan Swiderski
 */
public class SplitProof extends Proof {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.TerminationProofs");

    public SplitProof(){
    }

    public SplitProof (HaskellProgram oldHaskellProgram){
        super();
        this.name = "Split";
        this.shortName = "Split";
        this.longName = "Split";
    }

    /**
     * Formats the output string of the proof and returns it.
     */
    @Override
    public String export(Export_Util o) {
        StringBuffer result = new StringBuffer();
        result.append("Split Haskell Problem with startterms to Haskell problems with one startterm");
        return result.toString();
    };

    /**
     * Returns a BibTeX citation string for elements of this proof.
     */
    public String toBibTeX(){
        // No citations are given.
        return "";
    };
}
