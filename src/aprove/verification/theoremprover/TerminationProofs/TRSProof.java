package aprove.verification.theoremprover.TerminationProofs;

import java.io.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.TRSProblem.*;

/**
 * This class wraps all infos of a run of a TRS Processor.
 *
 * @author Martin Mertens
 * @version $Id$
 */
public abstract class TRSProof extends Proof implements Serializable {


    /**
     * Stores used TRS.
     */
    protected TRS trs;


    /**
     * Constructor.
     */
    public TRSProof(TRS trs) {
       this.trs = trs;
    }

    public TRSProof() {

    }

    /**
     * Returns proc input.
     */
    public TRS getOriginalTRS() {
    return this.trs;
    }

    public BasicObligation getBasicObligation() {
    return this.trs;
    }

    /**
     * Formats the output string of the proof and returns it.
     */
    @Override
    public abstract String export(Export_Util o);

    /**
     * Returns a HTML representation of the result.
     */
    @Override
    public String toHTML(){
       return this.export(new HTML_Util());
    }

    /**
     * Returns a LaTeX representation of the result.
     */
    @Override
    public String toLaTeX(){
        return this.export(new LaTeX_Util());
    }

    /**
     * Returns a BibTeX citation string for elements of this proof.
     */
    public abstract String toBibTeX();

    /**
     * Public getter method which should only be used by XMLEncoder.
     */
    public TRS getTrs() {
        return this.trs;
    }

    /**
     * Public setter method which should only be used by XMLDecoder.
     */
    public void setTrs(TRS trs) {
        this.trs = trs;
    }



}
