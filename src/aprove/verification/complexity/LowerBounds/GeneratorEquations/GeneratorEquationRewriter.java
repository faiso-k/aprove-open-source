package aprove.verification.complexity.LowerBounds.GeneratorEquations;

import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.Equation;
import aprove.verification.complexity.LowerBounds.EquationalUnification.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;

public class GeneratorEquationRewriter {

    private GeneratorEquations generatorRules;
    private PFHelper pfHelper;
    private EquationalUnifier unifier;

    public GeneratorEquationRewriter(GeneratorEquations generatorRules, PFHelper pfHelper, EquationalUnifier unifier) {
        super();
        this.generatorRules = generatorRules;
        this.pfHelper = pfHelper;
        this.unifier = unifier;
    }

    public boolean areEquivalent(TRSTerm s, TRSTerm t) {
        return this.normalizeRL(s).equals(this.normalizeRL(t));
    }

    public TRSTerm normalizeRL(TRSTerm tArg) {
        TRSTerm t = tArg;
        while (true) {
            TRSTerm newT = this.rewriteRL(t);
            if (newT == null) {
                return t;
            } else {
                t = newT;
            }
        }
    }

    private TRSTerm rewriteRL(TRSTerm t) {
        Set<Position> sortedPositions = new TreeSet<>(new OuterMostPositionComparator());
        sortedPositions.addAll(t.getPositions());
        for (Position pi : sortedPositions) {
            TRSTerm s = t.getSubterm(pi);
            TRSTerm newS = this.rewriteRootRL(s);
            newS = this.pfHelper.normalize(newS);
            if (!s.equals(newS)) {
                return t.replaceAt(pi, newS);
            }
        }
        return null;
    }

    private TRSTerm rewriteRootRL(TRSTerm t) {
        for (Equation rule : this.generatorRules) {
            TRSSubstitution sigma = this.unifier.match(rule.getRight(), t);
            if (sigma != null) {
                TRSTerm newT = rule.getLeft().applySubstitution(sigma);
                if (!t.equals(newT)) {
                    return newT;
                }
            }
        }
        return t;
    }
}
