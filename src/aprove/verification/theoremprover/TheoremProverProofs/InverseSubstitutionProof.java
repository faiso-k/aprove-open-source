package aprove.verification.theoremprover.TheoremProverProofs;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class InverseSubstitutionProof extends TheoremProverProof {

    protected Triple<TheoremProverObligation,AlgebraVariable,AlgebraTerm> inverseSubstitution;

    public InverseSubstitutionProof() {
    }

    public InverseSubstitutionProof(Triple<TheoremProverObligation,AlgebraVariable,AlgebraTerm> inverseSubstitution) {
        super();

        this.shortName  = "Inverse Substitution";
        this.longName    = "Inverse Substitution";

        this.inverseSubstitution = inverseSubstitution;
    }

    @Override
    public String export(Export_Util o) {
        if (Proof.CACHE_VALUES) {
                if (this.result.length() != 0) {
                    return this.result.toString();
                }
        } else {
            this.startUp();
        }

        StringBuffer stringBuffer = new StringBuffer();

        stringBuffer.append(o.bold("The formula could be generalised by inverse substitution to:"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.export(this.inverseSubstitution.x.getFormula()));
        stringBuffer.append(o.paragraph());
        stringBuffer.append(o.bold("Inverse substitution used:"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append("["+o.export(this.inverseSubstitution.z)+"/"+o.export(this.inverseSubstitution.y)+"]");
        stringBuffer.append(o.paragraph());

        return stringBuffer.toString();

    }

    public String toBibTeX() {
        return null;
    }

    @Override
    public Proof deepcopy() {
        return new InverseSubstitutionProof(new Triple<TheoremProverObligation,AlgebraVariable,AlgebraTerm>(this.inverseSubstitution.x.deepcopy(),
                (AlgebraVariable)this.inverseSubstitution.y.deepcopy(), this.inverseSubstitution.z.deepcopy()));
    }

    public Triple<TheoremProverObligation, AlgebraVariable, AlgebraTerm> getInverseSubstitution() {
        return this.inverseSubstitution;
    }

    public void setInverseSubstitution(
            Triple<TheoremProverObligation, AlgebraVariable, AlgebraTerm> inverseSubstitution) {
        this.inverseSubstitution = inverseSubstitution;
    }


}
