package aprove.verification.theoremprover.TerminationProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.*;

/**
 * This class wraps all infos of a run of a Processor.
 *
 * @author Martin Mertens, Achim Lücking
 */
public abstract class Proof extends aprove.prooftree.Proofs.Proof.DefaultProof implements HTML_Able, LaTeX_Able, PLAIN_Able {

    protected String name;

    public final static boolean CACHE_VALUES = false;

    //Yes, that's ugly...
    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        return super.export(o);
    }


    @Override
    public String toLaTeX() {
        return this.export(new LaTeX_Util());
    }


    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }


    @Override
    public String toPLAIN() {
        return this.export(new PLAIN_Util());
    }
}
