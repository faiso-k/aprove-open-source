package aprove.verification.dpframework.Orders;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * Polynomial orderings over the natural numbers where negative constants and
 * negative coefficients for variables are allowed. Here we do not use
 * approximations like [t]^left and [t]^right, but we represent max(.,0) directly.
 *
 * So far, we only recognize  t_1 rel t_2  if
 *  - t_1 rel t_2  has been part of the initial search problem from which we
 *    have obtained the polynomial interpretation or
 *  - rel == GE and one of {t_1 EQ t_2, t_1 GR t_2} is recognized
 *
 * @author fuhs
 * @version $Id$
 */
public class NegCoeffPOLO implements QActiveOrder, QActiveCondition.Afs {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.Orders.NegCoeffPOLO");

    final static String orderName = "Polynomial ordering with negative coefficients";

    private final NegCoeffPoloInterpretation interpretation;
    private final Map<TermPair, OrderRelation> elements;
    private final Abortion aborter;
    private final boolean checkSolves;

    private NegCoeffPOLO(final NegCoeffPoloInterpretation interpretation,
            final Map<TermPair, OrderRelation> elements, final Abortion aborter,
            final boolean checkSolves) {
        this.interpretation = interpretation;
        this.elements = elements;
        this.checkSolves = checkSolves;
        this.aborter = aborter;
    }

    /**
     *
     * @param interpretation - negative polynomial interpretation
     * @param elements - pairs of terms known to be in some relation
     *  (e.g., those used for which interpretation was found).
     * @return
     */
    public static NegCoeffPOLO create(final NegCoeffPoloInterpretation interpretation,
            final Map<TermPair, OrderRelation> elements, final Abortion aborter) {
        return new NegCoeffPOLO(interpretation, elements, aborter, true);
    }

    @Override
    public boolean solves(final Constraint<TRSTerm> c) throws AbortionException {
        return this.solves(c.getLeft(), c.getRight(), c.getType());
    }

    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) throws AbortionException {
        return this.solves(s, t, OrderRelation.GR);
    }

    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) throws AbortionException {
        return this.solves(s, t, OrderRelation.EQ);
    }

    private boolean solves(final TRSTerm l, final TRSTerm r, final OrderRelation queriedType) throws AbortionException {
        boolean result = false;
        final TermPair lhsAndRhs = TermPair.create(l, r);

        if (this.checkSolves) {
            final TRSTerm lhs = lhsAndRhs.getLhsInStandardRepresentation();
            final TRSTerm rhs = lhsAndRhs.getRhsInStandardRepresentation();
            return this.checkSolves(lhs, rhs, queriedType);
        }

        // Do we already have a known solution?
        OrderRelation rel = this.elements.get(lhsAndRhs);

        if (rel == null) {
            // maybe we have information on the flipped version of <l, r>,
            // i.e., <r, l>
            if (queriedType == OrderRelation.GE || queriedType == OrderRelation.EQ) {
                final TermPair rhsAndLhs = lhsAndRhs.flip();
                rel = this.elements.get(rhsAndLhs);
                if (Globals.useAssertions) {
                    assert rel == null || rel == OrderRelation.GE || rel == OrderRelation.EQ || rel == OrderRelation.GR;
                }
                if (rel == OrderRelation.EQ) {
                    result = true;
                }
            }
        }
        else {
            if (Globals.useAssertions) {
                assert rel == OrderRelation.GE || rel == OrderRelation.EQ || rel == OrderRelation.GR;
            }
            switch (queriedType) {
            case GE : {
                // any of GE, EQ, GR suffices here :-)
                result = true;
                break;
            }
            case EQ : {
                result = rel == OrderRelation.EQ;
                break;
            }
            case GR : {
                result = rel == OrderRelation.GR;
                break;
            }
            default:
                throw new RuntimeException("POLOs cannot handle constraint type "
                                           + rel + " !");
            }
        }

        return result;
    }

    /**
     * Checks whether l rel r holds by searching for suitable polynomials
     * as witnesses for the corresponding conditional constraints.
     *
     * @param l
     * @param r
     * @param queriedType
     * @return true if l rel r could be shown, false otherwise
     */
    private boolean checkSolves(final TRSTerm l, final TRSTerm r, final OrderRelation queriedType)
            throws AbortionException {
        long millis1, millis2;
        millis1 = System.currentTimeMillis();
        final OpVarPolynomial lPoly = this.interpretation.interpretTerm(l);
        OpVarPolynomial rPoly = this.interpretation.interpretTerm(r);

        ConstraintType cType;
        switch (queriedType) {
        case GE : {
            // any of GE, EQ, GR suffices here :-)
            cType = ConstraintType.GE;
            break;
        }
        case EQ : {
            cType = ConstraintType.EQ;
            break;
        }
        case GR : {
            rPoly = rPoly.plus(VarPolynomial.ONE);
            cType = ConstraintType.GE;
            break;
        }
        default:
            throw new RuntimeException("POLOs cannot handle constraint type "
                                       + queriedType + " !");
        }

        final OpVPC lrOpVPC = new OpVPC(lPoly, rPoly, cType);
        final VPSubstitutor substitutor = new VPSubstitutor();
        final Set<CondVPC> condVPCs = lrOpVPC.toCondVPCs(substitutor);

        if (condVPCs.isEmpty()) {
            millis2 = System.currentTimeMillis();
            if (Globals.DEBUG_FUHS && NegCoeffPOLO.log.isLoggable(Level.FINEST)) {
                NegCoeffPOLO.log.finest("Checking " + l + " " + queriedType + " " + r + " took " +
                    (millis2 - millis1) +
                    " ms in total. Explicit search was not necessary. Result: True!\n");
            }
            return true;
        }

        final Map<String, BigInteger> ranges = new LinkedHashMap<String, BigInteger>();
        final Set<VarPolyConstraint> vpcs = (new CondVPCToVPCTransformer()).transform(condVPCs,
                ranges);
        final Set<SimplePolyConstraint> spcs = new LinkedHashSet<SimplePolyConstraint>(3*vpcs.size());
        for (final VarPolyConstraint varPolyConstraint : vpcs) {
            Set<SimplePolyConstraint> absolutelyPositiveConstraints;
            absolutelyPositiveConstraints = varPolyConstraint.createCoefficientConstraints();
            spcs.addAll(absolutelyPositiveConstraints);
        }

        // now check using SAT4J (which is both always available and
        // very fast on small constraints)
        final SAT4JEngine.Arguments args = new SAT4JEngine.Arguments();
        args.andMode = SplitMode.UNFILTERED;
        args.orMode = SplitMode.UNFILTERED;
        final SAT4JEngine sat4jEngine = new SAT4JEngine(args);

        final DefaultValueMap<String, BigInteger> defValueRanges = new DefaultValueMap<String, BigInteger>(BigInteger.ONE);
        defValueRanges.putAll(ranges);

        final PoloSatConverter dioSatConv = PlainSPCToCircuitConverter.create(sat4jEngine.getFormulaFactory(), defValueRanges, BigInteger.ONE, new PoloSatConfigInfo());

        final SearchAlgorithm searchAlg = SatSearch.create(sat4jEngine, dioSatConv);
        /*
        SearchAlgorithm searchAlg;
        FormulaFactory<None> propFactory = new FullSharingFactory<None>();

        PoloSatConverter poloSatConverter = (new PLAINConverter()).getPoloSatConverter(propFactory,
                ranges, 1);

        // finally we get the search algorithm
        searchAlg = SatSearch.create(new SAT4JEngine(), poloSatConverter);
        */
        boolean result;
        final Map<String, BigInteger> solution = searchAlg.search(spcs,
                Collections.<SimplePolyConstraint>emptySet(), this.aborter);
        result = (solution != null);

        millis2 = System.currentTimeMillis();
        if (NegCoeffPOLO.log.isLoggable(Level.FINEST)) {
            NegCoeffPOLO.log.finest("Checking " + l + " " + queriedType + " " + r + " took " +
                (millis2 - millis1) + " ms in total. Result: " + result + "\n");
        }
        return result;
    }

    @Override
    public boolean checkQActiveCondition(QActiveCondition qac) {
        qac = qac.specialize(this);
        if (qac.isBoolean()) {
            return qac == QActiveCondition.TRUE;
        }
        else {
            throw new RuntimeException("qactive condition should be evaluatable at this point");
        }
    }

    @Override
    public YNM filterPosition(final FunctionSymbol f, final int i) {
        final VarPolynomial inter = this.interpretation.getInterpretation(f);
        if (inter == null) {
            return YNM.MAYBE;
        }
        final String x = NegCoeffPoloInterpretation.VAR_PREFIX+(i+1);
        final boolean posOccursInInter = inter.containsVariable(x);
        return YNM.fromBool(posOccursInInter);
    }


    @Override
    public String export(final Export_Util o) {
        return this.interpretation.export(o);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        throw new RuntimeException("no CPF export " + this.isCPFSupported());
    }

    @Override
    public String isCPFSupported() {
        return this.getClass().getCanonicalName();
    }

}
