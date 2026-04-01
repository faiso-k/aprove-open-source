package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * The proof for LA simplification
 *
 * Does not only show the new obligations but
 * first the dnf of the original formula, too.
 *
 * @author dickmeis
 * @version $Id$
 *
 */

public class LASimplificationProof extends TheoremProverProof {

    private Formula dnfFormula;

    private List<TheoremProverObligation> obligations;

    public LASimplificationProof() {
        this.name = "LA Simplification";
        this.shortName = "LA Simplification";
        this.longName = "LA Simplification";
    }

    public LASimplificationProof(Formula dnfFormula,
            List<TheoremProverObligation> obligations) {
        this.dnfFormula = dnfFormula;
        this.obligations = obligations;

        this.name = "LA Simplification";
        this.shortName = "LA Simplification";
        this.longName = "LA Simplification";
    }

    public LASimplificationProof(Formula dnfFormula,
            TheoremProverObligation obligation) {
        this.dnfFormula = dnfFormula;
        this.obligations = new ArrayList<TheoremProverObligation>(1);
        this.obligations.add(obligation);

        this.name = "LA Simplification";
        this.shortName = "LA Simplification";
        this.longName = "LA Simplification";
    }

    public LASimplificationProof(Formula dnfFormula) {
        this.dnfFormula = dnfFormula;
        this.obligations = null;

        this.name = "LA Simplification";
        this.shortName = "LA Simplification";
        this.longName = "LA Simplification";
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold(
                "The the formula to prove could be transformed into its dnf:"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.export(this.dnfFormula));
        stringBuffer.append(o.linebreak());

        if(this.obligations == null){
            stringBuffer.append(o.bold("This could be prooven to be true."));
        }
        else if(this.obligations.size() == 1){
            stringBuffer.append(o.bold(
                    "This could be reduced to the following new obligation by LA simplification:"));
            stringBuffer.append(o.linebreak());

            stringBuffer.append(o.export(this.obligations.get(0)));
        }
        else{
            stringBuffer.append(o.bold(
                    "This could be reduced to the following new obligations by LA simplification:"));
            stringBuffer.append(o.linebreak());

            stringBuffer.append(o.set(this.obligations, 3));
        }

        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {
        if(this.obligations == null){
            return new LASimplificationProof(this.dnfFormula.deepcopy());
        }
        else{
            ArrayList<TheoremProverObligation> newObligations =
                new ArrayList<TheoremProverObligation>(this.obligations.size());

            for (TheoremProverObligation obl : this.obligations) {
                TheoremProverObligation newObl = obl.deepcopy();
                newObligations.add(newObl);
            }
            return new LASimplificationProof(this.dnfFormula.deepcopy(),
                    newObligations);
        }
    }

}
