package aprove.verification.dpframework.HaskellProblem.Processors;

import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.HaskellProblem.*;

/**
 * @author Stephan Swiderski
 */
public class BindingReductionProof extends HaskellProof {
    protected static Logger logger = Logger.getLogger("aprove.verification.theoremprover.TerminationProofs");

    public BindingReductionProof(){
    }

    public BindingReductionProof (HaskellProgram oldHaskellProgram, HaskellProgram newHaskellProgram){
    super(oldHaskellProgram, newHaskellProgram);
    this.name = "BindingReduction";
    this.shortName = "BR";
    this.longName = "BindingReduction";
    }

    /**
     * Formats the output string of the proof and returns it.
     */
    @Override
    public String export(Export_Util o) {
        this.startUp();
        this.result.append("Replaced joker patterns by fresh variables and removed binding patterns.");
        if (this.reductions.size() > 0) {
            this.result.append(o.newline());
            this.result.append("Binding Reductions:");
            this.result.append(this.export(o,"The bind variable of the following binding Pattern","is replaced by the following term"));
        }
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
