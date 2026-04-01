package aprove.verification.theoremprover.TerminationProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.TRSProblem.*;

/**
 * This class wraps all infos of a run  of a CTRStoTRSProcessor.
 *
 * @author Stephan Swiderski
 * @version $Id$
 */
public class CTRStoTRSProof extends TRSProof {

    TRS newTRS;

    /**
     * The default contstuctor should only be used for XML serialization.
     */
    public CTRStoTRSProof() {

    }

    /**
     * Constructor.
     */
    public CTRStoTRSProof(TRS trs, TRS newTrs){
    super(trs);
    this.newTRS = newTrs;
    this.name = "CTRStoTRS";
    this.shortName = "CTRStoTRS";
    this.longName = "CTRS to TRS Transformation";
    }

    /**
     * Formats the output string of the proof and returns it.
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


        if (this.trs.getProgram().equals(this.newTRS.getProgram())) {
            // no output in this case
            return this.result.toString();
        }


        String out;
        boolean  tco = true;
        this.result.append(o.linebreak());
    this.result.append("Transformation form CTRS to TRS successful.");
        this.result.append(o.linebreak());
    this.result.append("Old CTRS:");
        this.result.append(o.linebreak());
    this.result.append(o.set(this.trs.getProgram().getRules(), Export_Util.RULES));
        this.result.append(o.linebreak());
    this.result.append("New TRS:");
        this.result.append(o.linebreak());
        this.result.append(o.set(this.newTRS.getProgram().getRules(), Export_Util.RULES));

        this.result.append(o.linebreak());

    return this.result.toString();
    }


    /**
     * Returns a BibTeX citation string for elements of this proof.
     */
    @Override
    public String toBibTeX(){
    // No citations are given.
    return "";
    }

    /**
     * Public getter method which should only be used by XMLEncoder.
     */
    public TRS getNewTRS() {
        return this.newTRS;
    }

    /**
     * Public setter method which should only be used by XMLDecoder.
     */
    public void setNewTRS(TRS newTRS) {
        this.newTRS = newTRS;
    };

}
