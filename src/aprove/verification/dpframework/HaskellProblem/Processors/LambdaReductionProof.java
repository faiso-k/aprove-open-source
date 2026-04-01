package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.HaskellProblem.*;

/**
 * @author Stephan Swiderski
 */
public class LambdaReductionProof extends HaskellProof {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.TerminationProofs");

    public LambdaReductionProof() {

    }

    public LambdaReductionProof (HaskellProgram oldHaskellProgram, HaskellProgram newHaskellProgram){
        super(oldHaskellProgram, newHaskellProgram);
        this.name = "LambdaReduction";
        this.shortName = "LR";
        this.longName = "LambdaReduction";
    }

    /**
     * Formats the output string of the proof and returns it.
     */
    @Override
    public String export(Export_Util o) {
        this.startUp();
        this.result.append("Lambda Reductions:");
        this.result.append(this.export(o,"The following Lambda expression","is transformed to"));
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
