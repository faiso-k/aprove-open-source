package aprove.verification.complexity.LowerBounds.ConjectureGeneration;

import java.math.*;
import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;
import aprove.verification.oldframework.SMT.Solver.SMTInterpol.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public abstract class ConjectureGenerationHeuristic {

    List<RewriteSequence> sampleConjectures;
    LowerBoundsToolbox toolbox;
    SMTInterpolIntSolver solver;
    SingleSampleConjectureToEqSystem sampleConjectureTransformer;
    SampleConjectureMap samplingPoints;
    ConjectureGenerationModel model;
    TRSSubstitution refinement;
    GroupingCriterion groupingCriterion;

    public ConjectureGenerationHeuristic(LowerBoundsToolbox toolbox, GroupingCriterion groupingCriterion) {
        this.toolbox = toolbox;
        this.groupingCriterion = groupingCriterion;
        this.sampleConjectures = new ArrayList<>();
        this.solver = new SMTInterpolIntSolverFactory().getSMTSolver(SMTLIBLogic.QF_LIA, toolbox.aborter);
        this.sampleConjectureTransformer = this.getSampleConjectureTransformer();
    }

    public boolean apply(NarrowingTree tree) {
        for (RewriteSequence sc: this.getRewriteSequencesToConsider(tree)) {
            if (this.isRelevant(sc)) {
                this.sampleConjectures.add(sc);
            }
        }
        SampleConjecturesToEqSystems transformer = this.getTransformer();
        return this.searchModel(transformer);
    }

    private boolean searchModel(SampleConjecturesToEqSystems transformer) {
        SampleConjectureMap samplingPoints = transformer.getSamplingPoints();
        if (samplingPoints != null && samplingPoints.size() >= this.requiredSamplingPoints()) {
            Pair<ConjectureGenerationModel, TRSSubstitution> p = this.searchAllCoefficients(transformer);
            if (p != null) {
                this.model = p.x;
                this.refinement = p.y;
                this.samplingPoints = samplingPoints;
                return true;
            }
        }
        return false;
    }

    /**
     * Tries to solve the linear equation system which results from the sample conjectures and returns the model (or
     * null if it fails to find one). Thereby, some variables may be instantiated heuristiacally. The instantiation is
     * the second component of the return value.
     */
    private Pair<ConjectureGenerationModel, TRSSubstitution> searchAllCoefficients(SampleConjecturesToEqSystems transformer) {
        Pair<LinearEqSystemMap, TRSSubstitution> p = transformer.transform();
        if (p == null) {
            return null;
        }
        LinearEqSystemMap linearEqSystems = p.x;
        TRSSubstitution refinement = p.y;
        List<NamedSymbol0<SInt>> coefficients = transformer.getCoefficients();
        ConjectureGenerationModel model = new ConjectureGenerationModel();
        for (RulePosition pos : linearEqSystems.keySet()) {
            Map<String, BigInteger> res = this.solve(linearEqSystems.get(pos), coefficients);
            if (res == null) {
                return null;
            } else {
                model.setModel(pos, res);
            }
        }
        return new Pair<>(model, refinement);
    }

    Map<String, BigInteger> solve(LinearEqSystem system, List<NamedSymbol0<SInt>> coefficients) {
        this.solver.addAssertion(system.getExpression());
        Map<String, BigInteger> res = null;
        if (this.solver.checkSAT() == YNM.YES) {
            res = new LinkedHashMap<>();
            for (NamedSymbol0<SInt> coefficient : coefficients) {
                res.put(coefficient.getName(), this.solver.getValue(SInt.representative, coefficient));
            }
        }
        this.solver.reset();
        return res;
    }

    public void reset() {
        this.sampleConjectures = new ArrayList<>();
        this.solver.reset();
    }

    TRSFunctionApplication getStartTerm() {
        assert !this.samplingPoints.isEmpty();
        return this.samplingPoints.iterator().next().getLhs();
    }

    abstract SingleSampleConjectureToEqSystem getSampleConjectureTransformer();
    abstract SampleConjecturesToEqSystems getTransformer();
    abstract List<RewriteSequence> getRewriteSequencesToConsider(NarrowingTree tree);
    abstract boolean isRelevant(RewriteSequence sc);
    abstract int requiredSamplingPoints();
    public abstract Conjecture getResult();

}
