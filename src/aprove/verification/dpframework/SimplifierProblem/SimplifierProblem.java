package aprove.verification.dpframework.SimplifierProblem;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;


/** A SimplifierProblem is to be processed by SimplifierProcessors
 * It results from a transformation TRS -> SimplifierProblem
 *
 * @author Matthias Raffelsieper
 */
public class SimplifierProblem extends DefaultBasicObligation implements HTML_Able,PLAIN_Able,LaTeX_Able {

    private SimplifierObligation sObl = null;

    public SimplifierProblem() {
        super("Simplifier Problem", "Simplifier Problem");
    }

    public SimplifierProblem(String shortName, String longName) {
        super(shortName, longName);
    }

    public SimplifierProblem(SimplifierObligation sObl) {
        super("Simplifier Problem", "Simplifier Problem");
        this.setSimplifierObligation(sObl);
    }

    public SimplifierProblem(String shortName, String longName, SimplifierObligation sObl) {
        this(shortName, longName);
        this.setSimplifierObligation(sObl);
    }

    // Getter,Setter
    public SimplifierObligation getSimplifierObligation() {
        return this.sObl;
    }

    public void setSimplifierObligation(SimplifierObligation sObl) {
        this.sObl = sObl;
    }



    @Override
    public String toHTML() {
        return this.sObl.toHTML();
    }

    @Override
    public String toPLAIN() {
        return this.sObl.toPLAIN();
    }

    @Override
    public String toLaTeX() {
        return this.sObl.toLaTeX();
    }

    @Override
    public String export(Export_Util util){
        return this.sObl.export(util);
    }


    @Override
    public SimplifierProblem deepcopy() {
        return new SimplifierProblem(this.getName(NameLength.SHORT), this.getName(NameLength.LONG), this.sObl.deepcopy());
    }

    @Override
    public BasicObligation maybeCopy() {
        return this;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
           throw new UnsupportedOperationException();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return null;
    }
}
