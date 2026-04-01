package aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem;

import java.math.*;
import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.ConjectureGeneration.SampleConjecturesToEqSystem.SingleSampleConjectureToEqSystem.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Transforms a set of narrowing sequences (which provides sampling points for the polynomials we are looking for)
 * to systems of linear equations (whose solution are the coefficients of the polynomials).
 */
public abstract class SampleConjecturesToEqSystems {

    private SingleSampleConjectureToEqSystem transformer;
    private SampleConjectureMap samplingPoints = null;
    private LinearEqSystemMap res = new LinearEqSystemMap();
    private GroupingCriterion groupingCriterion;
    private TRSTerm rhsScheme;
    private Map<BigInteger, SMTExpression<SInt>> polynomials = null;
    private LowerBoundsToolbox toolbox;

    public SampleConjecturesToEqSystems(Collection<RewriteSequence> sampleConjectures,
            GroupingCriterion groupingCriterion,
            SingleSampleConjectureToEqSystem transformer,
            LowerBoundsToolbox toolbox) {
        this.transformer = transformer;
        this.groupingCriterion = groupingCriterion;
        this.toolbox = toolbox;
        this.initSamplingPointInformation(sampleConjectures);
        if (this.samplingPoints != null) {
            this.rhsScheme = this.samplingPoints.getScheme();
        }
    }

    /**
     * Tries to find a subset of the given sequences whose elements are similar enough,
     * such that they might provide sampling points for the polynomial we are looking for
     */
    private void initSamplingPointInformation(Collection<RewriteSequence> sampleConjectures) {
        // we group the given sequences here and return the biggest group, in the end
        Set<SampleConjectureMap> groups = new LinkedHashSet<>();
        Set<RewriteSequence> interestingSampleConjectures = new LinkedHashSet<>();
        // we are only interested in sequences that loop at least one rule
        for (RewriteSequence sampleConjecture: sampleConjectures) {
            if (sampleConjecture.hasLoops()) {
                interestingSampleConjectures.add(sampleConjecture);
            }
        }
        for (RewriteSequence sampleConjecture: interestingSampleConjectures) {
            SampleConjectureMap existingMatchingSamplingPoints = null;
            /*
             * put the current sequence in the appropriate group by looking at its scheme
             * and the used base-case (i.e.: non-recursive) rules
             */
            for (SampleConjectureMap c: groups) {
                if (this.groupingCriterion.fits(c, sampleConjecture)) {
                    existingMatchingSamplingPoints = c;
                    break;
                }
            }
            SampleConjectureMap matchingGroup;
            if (existingMatchingSamplingPoints != null) {
                matchingGroup = existingMatchingSamplingPoints;
            } else {
                // create a new group, if necessary
                matchingGroup = this.newGroup(sampleConjecture, this.toolbox);
                if (matchingGroup == null) {
                    continue;
                }
                groups.add(matchingGroup);
            }
            matchingGroup.add(sampleConjecture);
        }
        // find and return the largest group
        if (!groups.isEmpty()) {
            this.samplingPoints = groups.iterator().next();
        }
        for (SampleConjectureMap c: groups) {
            if (c.size() > this.samplingPoints.size()) {
                this.samplingPoints = c;
            }
        }
        if (this.samplingPoints != null) {
            this.buildPolynomials();
        }
    }

    abstract SampleConjectureMap newGroup(RewriteSequence conjecture, LowerBoundsToolbox toolbox);

    /**
     * Transforms a set of sample conjectures into a linear equation system. Thereby, it heuristically instantiates some
     * variables with constants. This Instantiation is the second component of the return value.
     */
    public Pair<LinearEqSystemMap, TRSSubstitution> transform() {
        TRSSubstitution refinement = TRSSubstitution.EMPTY_SUBSTITUTION;
        if (this.samplingPoints != null) {
            for (BigInteger x: this.samplingPoints.availableSamplingPoints()) {
                this.transformer.init(this.samplingPoints.getSampleConjectureFor(x), this.samplingPoints.getCoefficients(), this.polynomials.get(x));
                try {
                    Pair<Map<RulePosition, LinearEqSystem>, TRSSubstitution> p = this.transformer.transform(refinement);
                    this.res.addAll(p.x);
                    refinement = refinement.compose(p.y);
                } catch (NotTransformableException e) {
                    return null;
                }
            }
        }
        return new Pair<>(this.res, refinement);
    }

    public TRSTerm getRhsScheme() {
        return this.rhsScheme;
    }

    public List<NamedSymbol0<SInt>> getCoefficients() {
        return this.samplingPoints.getCoefficients();
    }

    public SampleConjectureMap getSamplingPoints() {
        return this.samplingPoints;
    }

    /** Build the instances of the polynomial whose coefficients we are looking for, one for each sampling point. */
    public void buildPolynomials() {
        this.polynomials = new LinkedHashMap<>();
        for (BigInteger x : this.samplingPoints.availableSamplingPoints()) {
            List<SMTExpression<SInt>> monoms = new ArrayList<>();
            SMTExpression<SInt> poly = this.samplingPoints.getCoefficient(0);
            for (int exp = 1; exp < this.samplingPoints.size(); exp++) {
                SMTExpression<SInt> coefficient = this.samplingPoints.getCoefficient(exp);
                List<SMTExpression<SInt>> constant =
                        Collections.<SMTExpression<SInt>>singletonList(new IntConstant(x.pow(exp)));
                monoms.add(new LeftAssocCall<SInt, SInt>(LeftAssocSymbol.IntsTimes, coefficient, ImmutableCreator.create(constant)));
            }
            poly = monoms.isEmpty() ? poly : new LeftAssocCall<SInt, SInt>(LeftAssocSymbol.IntsAdd, poly, ImmutableCreator.create(monoms));
            this.polynomials.put(x, poly);
        }
    }

}
