package aprove.verification.oldframework.Algebra.Polynomials.SMTSearch;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Search for POLOs by using a reduction to SMT and then applying an SMT solver.
 * Can also be used for solving a Diophantine Formula given a PoloSmtConverter.
 * C defines something like Diophantine or MbyN...
 *
 * @author Christian Kuknat
 */
public class SMTSearch extends AbstractSearchAlgorithm {

    private static final Logger LOG = Logger
            .getLogger("aprove.verification.oldframework.Algebra.Polynomials.SMTSearch.DioSMTSearch");

    private long encodeTime;
    private long solveTime;
    private long decodeTime;

    private final SMTEngine smtChecker;


    private final boolean splitBeforeVisit;

    private final BeforeSplitter spliter;

    // The converter distinguishes which kind of transformation is done
    // (IntInterval, Rationals...)
    private final DioSMTConverter converter;

    public SMTSearch(final DefaultValueMap<String, BigInteger> ranges,
            final DioSMTConverter converter, final SMTEngine smtChecker,
            final boolean splitBeforeVisit, BeforeSplitter spliter) {
        super(ranges);
        this.converter = converter;
        this.smtChecker = smtChecker;
        this.splitBeforeVisit = splitBeforeVisit;
        this.spliter = spliter;
    }

    @Override
    public Map<String, BigInteger> search(
            final Set<SimplePolyConstraint> constraints,
            final Set<SimplePolyConstraint> searchStrictConstraints,
            final SimplePolynomial maxMe, final Abortion aborter)
            throws AbortionException {

        FormulaFactory<Diophantine> factory;
        factory = new FullSharingFactory<Diophantine>();

        final List<Formula<Diophantine>> conjuncts = new ArrayList<Formula<Diophantine>>();
        for (final SimplePolyConstraint spc : constraints) {
            final Diophantine dio = Diophantine.create(spc.getPolynomial(), spc
                    .getType());
            final Formula<Diophantine> f = factory.buildTheoryAtom(dio);
            conjuncts.add(f);
        }

        if (!searchStrictConstraints.isEmpty()) {
            List<Formula<Diophantine>> searchStrictEqAtoms;
            searchStrictEqAtoms = new ArrayList<Formula<Diophantine>>(
                    searchStrictConstraints.size());
            for (final SimplePolyConstraint spc : searchStrictConstraints) {
                final SimplePolynomial lhsMinusRhs = spc.getPolynomial();
                Pair<SimplePolynomial, SimplePolynomial> lhsAndRhs;
                lhsAndRhs = lhsMinusRhs.toPositivePair();

                final Diophantine eqProposition = Diophantine.create(
                        lhsAndRhs.x, lhsAndRhs.y, ConstraintType.EQ);
                final Formula<Diophantine> fEq = factory
                        .buildTheoryAtom(eqProposition);
                searchStrictEqAtoms.add(fEq);

                final Diophantine geProposition = Diophantine.create(
                        lhsAndRhs.x, lhsAndRhs.y, ConstraintType.GE);
                final Formula<Diophantine> fGe = factory
                        .buildTheoryAtom(geProposition);
                conjuncts.add(fGe);
            }
            final Formula<Diophantine> allEqual = factory
                    .buildAnd(searchStrictEqAtoms);
            final Formula<Diophantine> notAllEqual = factory.buildNot(allEqual);
            conjuncts.add(notAllEqual);
        }
        final Formula<Diophantine> dioFormula = factory.buildAnd(conjuncts);

        return this.search(dioFormula, aborter);
    }

    @Override
    public Map<String, BigInteger> search(
            final Set<SimplePolyConstraint> constraints,
            final Set<SimplePolyConstraint> searchStrictConstraints, final Abortion aborter)
            throws AbortionException {
        return this.search(constraints, searchStrictConstraints, null, aborter);
    }

    @Override
    public Map<String, BigInteger> search(final Formula<Diophantine> f,
            final Abortion aborter) throws AbortionException {

        long l1;
        long l2;

        FormulaFactory<SMTLIBTheoryAtom> factory;
        factory = new FullSharingFactory<SMTLIBTheoryAtom>();

        if (this.splitBeforeVisit) {
            final DiophantineToVarMonomPairVisitor varMonoms = new DiophantineToVarMonomPairVisitor();
            f.apply(varMonoms);
            final Set<String> variables = varMonoms.getVariables();
            final Set<IndefinitePart> monoms = varMonoms.getMonoms();
            this.converter.createOs(variables.size());
            switch (this.spliter) {
            case MIN_SET:
                this.converter.orderForMinimalSet(variables, monoms);
                break;
            case MO_IGNORE_EXPONENT:
                this.converter.orderMostOftenIgnoreExponent(variables, monoms);
                break;
            case MO_RESPECT_EXPONENT:
                this.converter.orderMostOftenRespectExponent(variables, monoms);
                break;
            default:
                break;
            }

        }

        TheoryConverterVisitor<Diophantine, SMTLIBTheoryAtom> visitor;
        visitor = new TheoryConverterVisitor<Diophantine, SMTLIBTheoryAtom>(
                factory, this.converter);

        l1 = System.nanoTime();

        final Formula<SMTLIBTheoryAtom> smtLinTempFormula = f.apply(visitor);

        // now just the interval for each variable has
        // to be set for the smt solver
        final SMTLIBIntConstant smtMin = SMTLIBIntConstant
                .create(DioSMTConverter.MIN_BOUND);

        final List<Formula<SMTLIBTheoryAtom>> intervalledList = new LinkedList<Formula<SMTLIBTheoryAtom>>();
        for (String indefinite : this.converter.getIntervalIndefs()) {
            final SMTLIBIntConstant smtMax = SMTLIBIntConstant
                    .create(this.converter.getValues().get(indefinite));

            // here the variables of the transformation have
            // to be stored for getting the result later on
            final SMTLIBIntVariable smtIndef = this.converter.getVariableMap()
                    .get(indefinite.toString());

            // a >= 0
            final SMTLIBIntGE greaterEqual1 = SMTLIBIntGE.create(smtIndef,
                    smtMin);
            final Formula<SMTLIBTheoryAtom> gE1Formula = factory
                    .buildTheoryAtom(greaterEqual1);
            intervalledList.add(gE1Formula);
            // max >= a
            final SMTLIBIntGE greaterEqual2 = SMTLIBIntGE.create(smtMax,
                    smtIndef);
            final Formula<SMTLIBTheoryAtom> gE2Formula = factory
                    .buildTheoryAtom(greaterEqual2);
            intervalledList.add(gE2Formula);
        }
        intervalledList.add(smtLinTempFormula);
        final Formula<SMTLIBTheoryAtom> smtLinFormula = factory
                .buildAnd(intervalledList);

        l2 = System.nanoTime();
        this.encodeTime = l2 - l1;
        if (SMTSearch.LOG.isLoggable(Level.FINER)) {
            SMTSearch.LOG
                    .log(
                            Level.FINER,
                            "Conversion and linearization via Integer Intervals of Formula<Diophantine> "
                                    + "with SimplePolynomial to Formula<SMTLIBIntCMP> took {0} ms.\n",
                            (this.encodeTime / 1000000));
        }
        // System.out.println("Time (ms) for constraints to Prop Logic: "
        // + (l2 - l1) / 1000000 + "ms");

        aborter.checkAbortion();

        final List<Formula<SMTLIBTheoryAtom>> formulas = new LinkedList<Formula<SMTLIBTheoryAtom>>();
        // Aim is having much assertions here eventually... I think
        formulas.add(smtLinFormula);

        l1 = System.nanoTime();
        YNM success;
        try {
            success = this.smtChecker.satisfiable(formulas, SMTLogic.QF_LIA, aborter);
        } catch (final WrongLogicException e) {
            System.err.println("Solver error: " + e.getErrorMessage());
            success = YNM.MAYBE;
        }

        l2 = System.nanoTime();
        // System.out.println("Time (ms) for Prop Logic to Dio model:   " +
        // (l2-l1)/1000000 + "ms");
        this.solveTime = l2 - l1;
        if (success == YNM.MAYBE || success == YNM.NO) {
            this.decodeTime = 0;
            return null;
        }

        final Map<String, BigInteger> result = new LinkedHashMap<String, BigInteger>();
        assert this.converter instanceof DioSMTConverter;
        for (final SMTLIBIntVariable var : ((DioSMTConverter) this.converter)
                .getVariableMap().values()) {
            result.put(var.getName(), var.getResultAsBigInteger());
        }

        return result;
    }
    
    @Override
    public Map<String, BigInteger> searchLRA(final Formula<Diophantine> f,
            final Abortion aborter) throws AbortionException {

        long l1;
        long l2;

        FormulaFactory<SMTLIBTheoryAtom> factory;
        factory = new FullSharingFactory<SMTLIBTheoryAtom>();

        if (this.splitBeforeVisit) {
            final DiophantineToVarMonomPairVisitor varMonoms = new DiophantineToVarMonomPairVisitor();
            f.apply(varMonoms);
            final Set<String> variables = varMonoms.getVariables();
            final Set<IndefinitePart> monoms = varMonoms.getMonoms();
            this.converter.createOs(variables.size());
            switch (this.spliter) {
            case MIN_SET:
                this.converter.orderForMinimalSet(variables, monoms);
                break;
            case MO_IGNORE_EXPONENT:
                this.converter.orderMostOftenIgnoreExponent(variables, monoms);
                break;
            case MO_RESPECT_EXPONENT:
                this.converter.orderMostOftenRespectExponent(variables, monoms);
                break;
            default:
                break;
            }

        }

        TheoryConverterVisitor<Diophantine, SMTLIBTheoryAtom> visitor;
        visitor = new TheoryConverterVisitor<Diophantine, SMTLIBTheoryAtom>(
                factory, this.converter);

        l1 = System.nanoTime();

        final Formula<SMTLIBTheoryAtom> smtLinTempFormula = f.apply(visitor);

        // now just the interval for each variable has
        // to be set for the smt solver
        final SMTLIBIntConstant smtMin = SMTLIBIntConstant
                .create(DioSMTConverter.MIN_BOUND);

        final List<Formula<SMTLIBTheoryAtom>> intervalledList = new LinkedList<Formula<SMTLIBTheoryAtom>>();
        for (String indefinite : this.converter.getIntervalIndefs()) {
            final SMTLIBIntConstant smtMax = SMTLIBIntConstant
                    .create(this.converter.getValues().get(indefinite));

            // here the variables of the transformation have
            // to be stored for getting the result later on
            final SMTLIBIntVariable smtIndef = this.converter.getVariableMap()
                    .get(indefinite.toString());

            // a >= 0
            final SMTLIBIntGE greaterEqual1 = SMTLIBIntGE.create(smtIndef,
                    smtMin);
            final Formula<SMTLIBTheoryAtom> gE1Formula = factory
                    .buildTheoryAtom(greaterEqual1);
            intervalledList.add(gE1Formula);
            // max >= a
            final SMTLIBIntGE greaterEqual2 = SMTLIBIntGE.create(smtMax,
                    smtIndef);
            final Formula<SMTLIBTheoryAtom> gE2Formula = factory
                    .buildTheoryAtom(greaterEqual2);
            intervalledList.add(gE2Formula);
        }
        intervalledList.add(smtLinTempFormula);
        final Formula<SMTLIBTheoryAtom> smtLinFormula = factory
                .buildAnd(intervalledList);

        l2 = System.nanoTime();
        this.encodeTime = l2 - l1;
        if (SMTSearch.LOG.isLoggable(Level.FINER)) {
            SMTSearch.LOG
                    .log(
                            Level.FINER,
                            "Conversion and linearization via Integer Intervals of Formula<Diophantine> "
                                    + "with SimplePolynomial to Formula<SMTLIBIntCMP> took {0} ms.\n",
                            (this.encodeTime / 1000000));
        }
        // System.out.println("Time (ms) for constraints to Prop Logic: "
        // + (l2 - l1) / 1000000 + "ms");

        aborter.checkAbortion();

        final List<Formula<SMTLIBTheoryAtom>> formulas = new LinkedList<Formula<SMTLIBTheoryAtom>>();
        // Aim is having much assertions here eventually... I think
        formulas.add(smtLinFormula);

        l1 = System.nanoTime();
        YNM success;
        try {
            success = this.smtChecker.satisfiable(formulas, SMTLogic.QF_LRA, aborter);
        } catch (final WrongLogicException e) {
            System.err.println("Solver error: " + e.getErrorMessage());
            success = YNM.MAYBE;
        }

        l2 = System.nanoTime();
        // System.out.println("Time (ms) for Prop Logic to Dio model:   " +
        // (l2-l1)/1000000 + "ms");
        this.solveTime = l2 - l1;
        if (success == YNM.MAYBE || success == YNM.NO) {
            this.decodeTime = 0;
            return null;
        }

        final Map<String, BigInteger> result = new LinkedHashMap<String, BigInteger>();
        assert this.converter instanceof DioSMTConverter;
        for (final SMTLIBIntVariable var : ((DioSMTConverter) this.converter)
                .getVariableMap().values()) {
            result.put(var.getName(), var.getResultAsBigInteger());
        }

        return result;
    }
    

}