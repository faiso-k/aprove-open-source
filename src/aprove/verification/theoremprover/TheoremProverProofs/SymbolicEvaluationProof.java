/*
 * Created on 09.07.2004
 *
 * @author Ralf Behle
 */
package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.theoremprover.TerminationProofs.*;

/**
 * Class represents a proof used for symbolic evaluation
 * @author rabe
 * @version $Id$
 */
public class SymbolicEvaluationProof extends TheoremProverProof {

    /**
     * obligation remaining to be proved
     */
    protected TheoremProverObligation newObligation;

    public SymbolicEvaluationProof() {
    }

    public SymbolicEvaluationProof(final TheoremProverObligation newObligation) {

        this.name = "Symbolic evaluation";
        this.longName = "Symbolic evaluation";
        this.shortName = "Symbolic evaluation";

        this.newObligation = newObligation;

    }

    @Override
    public String export(final Export_Util o) {
        if (Proof.CACHE_VALUES) {
            if (this.result.length() != 0) {
                return this.result.toString();
            }
        } else {
            this.startUp();
        }

        if (this.newObligation.getTruthValue().equals(YNM.YES)) {
            this.result.append(o.bold("Could be shown by simple symbolic evaluation."));
        } else if (this.newObligation.getTruthValue().equals(YNM.NO)) {
            this.result.append(o.bold("Could be disproved by simple symbolic evaluation."));
        } else {
            this.result.append(o.bold("Could be reduced to the following new obligation by simple symbolic evaluation:"));
            this.result.append(o.linebreak());
            this.result.append(o.export(this.newObligation.getFormula()));
        }

        return this.result.toString();
    }

    public TheoremProverObligation getNewObligation() {
        return this.newObligation;
    }

    public void setNewObligation(final TheoremProverObligation newObligation) {
        this.newObligation = newObligation;
    }

    @Override
    public Proof deepcopy() {
        return new SymbolicEvaluationProof(this.newObligation.deepcopy());
    }

}
