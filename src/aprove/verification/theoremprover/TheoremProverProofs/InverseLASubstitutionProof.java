package aprove.verification.theoremprover.TheoremProverProofs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TerminationProofs.*;

public class InverseLASubstitutionProof extends TheoremProverProof {

    private List<Pair<AlgebraTerm, Position>>  candidates;
    private AlgebraVariable freshVar;
    private TheoremProverObligation newObligation;

    public InverseLASubstitutionProof(TheoremProverObligation newObligation, List<Pair<AlgebraTerm, Position>> bestCandidate, AlgebraVariable freshVar) {
        super();

        this.shortName  = "Inverse LA Substitution";
        this.longName   = "Inverse LA Substitution";

        this.candidates = new ArrayList<Pair<AlgebraTerm,Position>>(bestCandidate.size());
        for (Pair<AlgebraTerm, Position> pair : bestCandidate) {
            Pair<AlgebraTerm, Position> p = new Pair<AlgebraTerm, Position>(pair.x.deepcopy(), pair.y.deepcopy());
            this.candidates.add(p);
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

        stringBuffer.append(o.bold("The LA terms"));
        stringBuffer.append(o.linebreak());
        for (Pair<AlgebraTerm, Position> pair : this.candidates) {
            stringBuffer.append(pair.x.export(o));
            stringBuffer.append(o.linebreak());
        }
        stringBuffer.append(o.bold("are equal. "));
        stringBuffer.append(o.linebreak());

        stringBuffer.append(o.bold("They have gotten replaced by the new Variable: "));
        stringBuffer.append(this.freshVar.export(o));
        stringBuffer.append(o.linebreak());

        stringBuffer.append(o.bold("By this the formula could be generalised by inverse LA substitution to the new formula:"));
        stringBuffer.append(o.linebreak());
        stringBuffer.append(o.export(this.newObligation.getFormula()));

        return stringBuffer.toString();
    }

    @Override
    public Proof deepcopy() {
        TheoremProverObligation newNewObl = this.newObligation.deepcopy();

        ArrayList<Pair<AlgebraTerm, Position>> newCandidates = new ArrayList<Pair<AlgebraTerm,Position>>(this.candidates.size());
        for (Pair<AlgebraTerm, Position> pair : this.candidates) {
            Pair<AlgebraTerm, Position> p = new Pair<AlgebraTerm, Position>(pair.x.deepcopy(), pair.y.deepcopy());
            newCandidates.add(p);
        }

        AlgebraVariable newFreshVar = (AlgebraVariable) this.freshVar.deepcopy();

        return new InverseLASubstitutionProof(newNewObl, newCandidates, newFreshVar);
    }

}
