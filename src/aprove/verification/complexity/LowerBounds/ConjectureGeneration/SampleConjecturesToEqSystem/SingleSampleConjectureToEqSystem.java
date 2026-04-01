package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.RulePosition.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public abstract class SingleSampleConjectureToEqSystem {

    @SuppressWarnings("serial")
    public class NotTransformableException extends Exception {
    }

    RewriteSequence sampleConjecture;
    private Map<RulePosition, LinearEqSystem> constraints = new LinkedHashMap<>();
    private SMTExpression<SInt> poly;
    LowerBoundsToolbox toolbox;
    private Collection<NamedSymbol0<SInt>> coefficients;


    public SingleSampleConjectureToEqSystem(LowerBoundsToolbox toolbox) {
        this.toolbox = toolbox;
    }

    void init(RewriteSequence sampleConjecture, Collection<NamedSymbol0<SInt>> coefficients, SMTExpression<SInt> poly) {
        this.sampleConjecture = sampleConjecture;
        this.poly = poly;
        this.coefficients = coefficients;
    }

    /**
     * Transforms a single sample conjecture into linear equations. Thereby, the given refinement has to be taken into
     * account and may be extended heuristically. The extended refinement is the second component of the return value.
     */
    Pair<Map<RulePosition, LinearEqSystem>, TRSSubstitution> transform(TRSSubstitution oldRefinement) throws NotTransformableException {
        TRSSubstitution refinement = this.transformLhs(oldRefinement);
        this.transformRhs(refinement);
        this.forceNat();
        Map<RulePosition, LinearEqSystem> res = this.constraints;
        this.constraints = new LinkedHashMap<>();
        return new Pair<>(res, refinement);
    }

    private void forceNat() {
        for (NamedSymbol0<SInt> c: this.coefficients) {
            SMTExpression<SBool> exp = Ints.greaterEqual(c, Ints.constant(0));
            Map<RulePosition, LinearEqSystem> newConstraints = new LinkedHashMap<>();
            for (Entry<RulePosition,  LinearEqSystem> e: this.constraints.entrySet()) {
                RulePosition pos = e.getKey();
                LinearEqSystem eqSystem = e.getValue();
                newConstraints.put(pos, eqSystem.and(exp));
            }
            this.constraints = newConstraints;
        }
    }

    /**
     * Transforms the lhs of a sample conjecture into linear equations. Thereby, the given refinement has to be taken
     * into account and may be extended heuristically. The extended refinement is the return value.
     */
    private TRSSubstitution transformLhs(TRSSubstitution oldRefinement) throws NotTransformableException {
        TRSSubstitution refinement = oldRefinement;
        TRSTerm lhsScheme = this.sampleConjecture.getStartTerm();
        Map<TRSVariable, List<Position>> varPositions = lhsScheme.getVariablePositions();
        TRSSubstitution sigma = this.sampleConjecture.composeSubstitutions();
        for (TRSVariable var : varPositions.keySet()) {
            List<Position> positions = varPositions.get(var);
            assert positions.size() == 1;
            if (sigma.getDomain().contains(var)) {
                TRSTerm t = this.toolbox.pfHelper.normalize(var.applySubstitution(sigma).applySubstitution(refinement));
                if (!PFHelper.isInt(t) && PFHelper.isArithFunction(t)) {
                    boolean changed;
                    do {
                        changed = false;
                        if (t.isVariable()) {
                            refinement = refinement.compose(TRSSubstitution.create((TRSVariable) t, PFHelper.ZERO.getTerm()));
                            t = t.applySubstitution(refinement);
                            t = this.toolbox.pfHelper.normalize(t);
                        } else {
                            for (Entry<TRSVariable, List<Position>> e : t.getVariablePositions().entrySet()) {
                                assert !e.getValue().isEmpty();
                                TRSVariable x = e.getKey();
                                Position pi = e.getValue().iterator().next().shorten(1);
                                FunctionSymbol root = ((TRSFunctionApplication) t.getSubterm(pi)).getRootSymbol();
                                TRSTerm oldT = t;
                                refinement = refinement.compose(TRSSubstitution.create(x, PFHelper.getNeutralElement(root)));
                                t = t.applySubstitution(refinement);
                                t = this.toolbox.pfHelper.normalize(t);
                                if (!t.equals(oldT)) {
                                    changed = true;
                                    break;
                                }
                            }
                        }
                    } while (changed);
                }
                this.addConstraint(Side.LEFT, positions.get(0), t);
            }
        }
        return refinement;
    }

    /**
     * Transforms the rhs of a sample conjecture into linear equations. Thereby, the given refinement has to be taken
     * into account.
     */
    abstract void transformRhs(TRSSubstitution refinement) throws NotTransformableException;

    void addConstraint(Side side, Position pos, TRSTerm t) throws NotTransformableException {
        if (!PFHelper.isInt(t)) {
            throw new NotTransformableException();
        }
        BigInteger val = PFHelper.toInt(t);
        LinearEqSystem newConstraint = LinearEqSystem.equivalent(this.poly, val);
        this.constraints.put(new RulePosition(side, pos), newConstraint);
    }
}
