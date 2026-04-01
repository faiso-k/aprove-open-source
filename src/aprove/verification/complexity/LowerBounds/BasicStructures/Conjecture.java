package aprove.verification.complexity.LowerBounds.BasicStructures;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.ConjectureProving.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Util.Transformations.*;
import aprove.verification.dpframework.BasicStructures.*;


public class Conjecture extends Relation<TRSFunctionApplication, TRSTerm, Conjecture> {

    public Conjecture(TRSFunctionApplication lhs, TRSTerm rhs) {
        super(lhs, rhs);
    }

    @Override
    Conjecture cloneWith(TRSFunctionApplication newLhs, TRSTerm newRhs) {
        return new Conjecture(newLhs, newRhs);
    }

    @Override
    String getSymbol(Export_Util eu) {
        String res = eu.rightarrow();
        res += eu.sup(eu.escape("?"));
        return res;
    }

    public Lemma toLemma(Complexity complexity) {
        return new Lemma(this, complexity);
    }

    public int getDegreeOfStartTermSize(TrsTypes types) {
        return new TermToSumOfPolynomials(types).transform(this.getLeft()).getDegree();
    }

    public ConjectureProver getProver(LowerBoundsToolbox toolbox,
            TermRewriter rewriter) {
        if (this.rhs.equals(toolbox.arbitraryTerm)) {
            return new IndefiniteConjectureProver(toolbox, rewriter, this);
        } else {
            return new DefiniteConjectureProver(toolbox, rewriter, this);
        }
    }

    public Conjecture toIndefiniteConjecture(LowerBoundsToolbox toolbox) {
        return new Conjecture(this.lhs, toolbox.arbitraryTerm);
    }


}
