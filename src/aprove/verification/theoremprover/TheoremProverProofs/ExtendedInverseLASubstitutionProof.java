package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class ExtendedInverseLASubstitutionProof extends TheoremProverProof {

    private List<Triple<Position, AlgebraTerm, AlgebraTerm>>  proofInfo;
    private AlgebraVariable freshVar;
    private TheoremProverObligation newObligation;

    public ExtendedInverseLASubstitutionProof(TheoremProverObligation newObligation,
            List<Triple<Position, AlgebraTerm, AlgebraTerm>> proofInfo, AlgebraVariable freshVar) {

        super();

        this.shortName  = "Extended Inverse LA Substitution";
        this.longName   = "Extended Inverse LA Substitution";

        this.proofInfo = new ArrayList<Triple<Position, AlgebraTerm, AlgebraTerm>>(proofInfo.size());
        for (Triple<Position, AlgebraTerm, AlgebraTerm> triple : proofInfo) {
            Triple<Position, AlgebraTerm, AlgebraTerm> t = new Triple<Position, AlgebraTerm, AlgebraTerm>(triple.x.deepcopy(), triple.y.deepcopy() , triple.z.deepcopy());
            this.proofInfo.add(t);
        }

        this.freshVar = (AlgebraVariable) freshVar.deepcopy();

        this.newObligation = newObligation.deepcopy();

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

        stringBuffer.append("We replaced the term " + this.proofInfo.get(0).y + "by the fresh new variable " + this.freshVar + ".");
        stringBuffer.append(o.linebreak());

        stringBuffer.append(o.bold("Therefore we made these replacements:"));
        stringBuffer.append(o.linebreak());

        for (Triple<Position, AlgebraTerm, AlgebraTerm> triple : this.proofInfo) {
            stringBuffer.append("The term " + triple.y.export(o) + " at position " + triple.x + " was replaced by " + triple.z.export(o));
            stringBuffer.append(o.linebreak());
        }

        stringBuffer.append(o.bold("By this the formula could be generalised by extended inverse LA substitution to the new formula:"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.export(this.newObligation.getFormula()));

        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {
        TheoremProverObligation newNewObl = this.newObligation.deepcopy();

        ArrayList<Triple<Position, AlgebraTerm, AlgebraTerm>> newProofInfo = new ArrayList<Triple<Position, AlgebraTerm, AlgebraTerm>>(this.proofInfo.size());
        for (Triple<Position, AlgebraTerm, AlgebraTerm> triple : this.proofInfo) {
            Triple<Position, AlgebraTerm, AlgebraTerm> t =
                new Triple<Position, AlgebraTerm, AlgebraTerm>(triple.x.deepcopy(), triple.y.deepcopy(), triple.z.deepcopy());
            newProofInfo.add(t);
        }

        AlgebraVariable newFreshVar = (AlgebraVariable) this.freshVar.deepcopy();

        return new ExtendedInverseLASubstitutionProof(newNewObl, newProofInfo, newFreshVar);
    }

}
