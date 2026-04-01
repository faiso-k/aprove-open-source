package aprove.verification.dpframework.Orders.SizeChangeNP.OrderEncoders;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Encode the constraints for polynomial orders.
 *
 * @author Carsten Fuhs
 */
public class SCNPPoloEncoder implements SCNPOrderEncoder {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.SizeChangeNP.OrderEncoders.SCNPPoloEncoder");

    private final FormulaFactory<None> ffactory;
    private final PoloSatConverter poloSatConverter;
    private final IndefiniteConverter<String> binarizer;
    private final BigInteger range;
    private final int degree;
    private final int maxSimpleDegree;
    private final boolean linearMonotone;

    private Interpretation interpretation;

    private final Map<TermPair, VarPolynomial> termPairInterpretation;
    private final Formula<None> ZERO, ONE;

    public SCNPPoloEncoder(FormulaFactory<None> formulaFactory,
            DiophantineSATConverter satConverter,
            BigInteger range, int degree,
            int maxSimpleDegree, boolean linearMonotone) {
        this.ffactory = formulaFactory;
        this.range = range;
        this.degree = degree;
        this.maxSimpleDegree = maxSimpleDegree;
        this.linearMonotone = linearMonotone;

        Map<String, BigInteger> ranges = new LinkedHashMap<String, BigInteger>(0);
        this.poloSatConverter = satConverter.getPoloSatConverter(this.ffactory, ranges, this.range);
        this.binarizer = this.poloSatConverter.getBinarizer();

        this.termPairInterpretation = new LinkedHashMap<TermPair, VarPolynomial>();
        this.ZERO = formulaFactory.buildConstant(false);
        this.ONE = formulaFactory.buildConstant(true);

        // pre() inits this field
        this.interpretation = null;
    }

    @Override
    public QActiveOrder decode(int[] model, Abortion aborter)
            throws AbortionException {
        Map<String, BigInteger> dioSolution = this.getDioSolution(model, aborter);
        Interpretation concreteInterpretation =
            this.interpretation.specialize(dioSolution, BigInteger.ZERO);
        POLO polo = POLO.create(concreteInterpretation);
        return polo;
    }

    /**
     * @param satModel
     * @param aborter
     * @return the Diophantine solution that corresponds to the given
     *  propositional solution <code>satModel</code>
     */
    private Map<String, BigInteger> getDioSolution(int[] satModel, Abortion aborter) {
        long l1 = System.nanoTime();
        // get the logical interpretation
        Set<Integer> satInterpretation;
        // x \in interpretation <=> x |-> true

        satInterpretation = new HashSet<Integer>(satModel.length);
        for (int i = 0; i < satModel.length; ++i) {
            if (satModel[i] > 0) {
                satInterpretation.add(satModel[i]);
            }
        }

        Map<String, PolyCircuit> indefToPolyCircuits = this.binarizer.getIndefsToVars();
        Map<String, BigInteger> result = new LinkedHashMap<String, BigInteger>(indefToPolyCircuits.size());
        for (Map.Entry<String, PolyCircuit> e : indefToPolyCircuits.entrySet()) {
            PolyCircuit pc = e.getValue();
            List<Formula<None>> formulae = pc.getFormulae();
            BigInteger coeffValue = this.binarizer.natBig(formulae, satInterpretation);
            if (Globals.useAssertions) {
                if (this.poloSatConverter.getTracking()) {
                    assert coeffValue.compareTo(pc.getMax()) <= 0;
                }
            }
            result.put(e.getKey(), coeffValue);
            if (SCNPPoloEncoder.log.isLoggable(Level.FINEST)) {
                SCNPPoloEncoder.log.log(Level.FINEST, "{0} ", e);
            }
        }
        long l2 = System.nanoTime();
        long decodeTime = l2 - l1;
        if (SCNPPoloEncoder.log.isLoggable(Level.FINEST)) {
            SCNPPoloEncoder.log.log(Level.FINEST, "\n");
        }
        if (SCNPPoloEncoder.log.isLoggable(Level.FINER)) {
            SCNPPoloEncoder.log.log(Level.FINER, "Decode time: {0} ms\n", decodeTime / 1000000l);
            SCNPPoloEncoder.log.finer("Diophantine solution: " +
                    new TreeMap<String, BigInteger>(result) + "\n");
        }
        return result;
    }

    @Override
    public Formula<None> pre(Set<FunctionSymbol> sig,
            Abortion aborter) throws AbortionException {
        this.interpretation = Interpretation.createForSignature(sig,
                this.degree, this.maxSimpleDegree, this.linearMonotone,
                false, aborter);
        return this.ONE;
    }

    @Override
    public Formula<None> encode(Constraint<TRSTerm> c, Abortion aborter)
            throws AbortionException {
        Set<SimplePolyConstraint> spcs = this.encodeToSPCs(c, aborter);
        if (spcs == null) {
            return this.ZERO;
        }
        Formula<None> converted = this.poloSatConverter.convertIteratively(spcs,
                aborter);
        return converted;
    }

    /**
     *
     * @param c
     * @param aborter
     * @return corresponding SPCs; null means unsatisfiable
     * @throws AbortionException
     */
    private Set<SimplePolyConstraint> encodeToSPCs(Constraint<TRSTerm> c,
            Abortion aborter) throws AbortionException {
        TRSTerm l = c.x;
        TRSTerm r = c.y;
        TermPair lr = TermPair.create(l, r);
        VarPolynomial diffPoly = this.termPairInterpretation.get(lr);
        if (diffPoly == null) {
            VarPolynomial leftPoly = this.interpretation.interpretTerm(c.x, aborter);
            VarPolynomial rightPoly = this.interpretation.interpretTerm(c.y, aborter);
            diffPoly = leftPoly.minus(rightPoly);
            this.termPairInterpretation.put(lr, diffPoly);
        }
        Set<SimplePolynomial> varCoeffs = diffPoly.getCoefficientsOfVariables();
        SimplePolynomial constantAddend = diffPoly.getConstantPart();

        Set<SimplePolyConstraint> spcs = new LinkedHashSet<SimplePolyConstraint>(varCoeffs.size()+1);
        for (SimplePolynomial sp : varCoeffs) {
            SimplePolyConstraint spc = new SimplePolyConstraint(sp, ConstraintType.GE);
            if (! spc.isSatisfiable()) {
                return null;
            }
            if (! spc.isValid()) {
                spcs.add(spc);
            }
        }
        OrderRelation rel = c.z;
        ConstraintType ct;
        switch (rel) {
        case GE:
            ct = ConstraintType.GE;
            break;
        case GR:
            ct = ConstraintType.GT;
            break;
        default:
            throw new RuntimeException("Cannot handle relation: " + rel);
        }
        SimplePolyConstraint spc = new SimplePolyConstraint(constantAddend, ct);
        if (! spc.isSatisfiable()) {
            return null;
        }
        if (! spc.isValid()) {
            spcs.add(spc);
        }
        return spcs;
    }

    @Override
    public Formula<None> encodeQActiveAtom(FunctionSymbol f, int i, Abortion aborter) throws AbortionException {
        VarPolynomial pol = this.interpretation.get(f);
        String var = Interpretation.VARIABLE_PREFIX + (i+1);
        SimplePolynomial sp = pol.getSumOfCoefficientPolys(var);
        SimplePolyConstraint spc = new SimplePolyConstraint(sp, ConstraintType.GT);
        if (! spc.isSatisfiable()) {
            return this.ZERO;
        }
        if (spc.isValid()) {
            return this.ONE;
        }
        Set<SimplePolyConstraint> spcs =
            java.util.Collections.<SimplePolyConstraint>singleton(spc);
        Formula<None> converted =
            this.poloSatConverter.convertIteratively(spcs, aborter);
        return converted;
    }

    @Override
    public Formula<None> post(Abortion aborter) throws AbortionException {
        List<Formula<None>> conjuncts = this.binarizer.getSideConstraints();
        Formula<None> result = this.ffactory.buildAnd(conjuncts);
        return result;
    }

    @Override
    public Formula<None> toFinalFormula(Formula<None> f, Abortion aborter)
            throws AbortionException {
        return f;
    }

    @Override
    public FormulaFactory<None> getFormulaFactory() {
        return this.ffactory;
    }
}
