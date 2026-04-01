package aprove.verification.idpframework.Processors.NonInf.Solving;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SATDumpEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Monomial;
import aprove.verification.idpframework.Polynomials.Polynomial;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Polynomials.Interpretation.PolyInterpretation.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author MP
 */
public class ItpfPolyDiophantineSatSolver implements
        ItpfPolyConstraintsSolver {

    private static final SemiRingDomain<BigInt> DEFAULT_VAR_RANGE = DomainFactory.createVarRange(BigInt.ZERO, BigInt.create(BigInteger.valueOf(-1)), BigInt.create(BigInteger.valueOf(2)));

    @Override
    public PolyInterpretation<BigInt> solve(final IDPPredefinedMap predefinedMap,
        final PolyInterpretation<BigInt> abstractInterpretation,
        final Conjunction<Itpf> constraints,
        final Abortion aborter) throws AbortionException {
        return this.solve(predefinedMap, abstractInterpretation, constraints, ItpfPolyDiophantineSatSolver.DEFAULT_VAR_RANGE, aborter);
    }

    public PolyInterpretation<BigInt> solve(final IDPPredefinedMap predefinedMap,
        final PolyInterpretation<BigInt> abstractInterpretation, final Conjunction<Itpf> constraints,
        final SemiRingDomain<BigInt> defaultVarRange, final Abortion aborter) throws AbortionException {

        final BidirectionalMap<IVariable<BigInt>, String> varMapping = new BidirectionalMap<IVariable<BigInt>, String>();

        final Map<String, BigInteger> varRanges = new LinkedHashMap<String, BigInteger>();
        final Map<IVariable<BigInt>, SimplePolynomial> varPolys = new LinkedHashMap<IVariable<BigInt>, SimplePolynomial>();

        final FormulaFactory<Diophantine> diophantineFormulaFactory =
            new FullSharingFactory<Diophantine>();

        final Formula<Diophantine> diophantineFormula = this.createDiophantineFormula(diophantineFormulaFactory,
            constraints,
            abstractInterpretation,
            varMapping,
            varRanges,
            varPolys,
            defaultVarRange,
            aborter);

        if (Globals.DEBUG_MPLUECKER) {
            this.traceConstraints(constraints);
            this.traceDiophantineFormula(diophantineFormula);
        }

        final PoloSatConfigInfo satConfig = new PoloSatConfigInfo();
        final BigInteger defaultRange = BigInteger.valueOf(4);

        final FormulaFactory<None> formulaFactory = new FullSharingFactory<None>();

        final CachingSPCToCircuitConverter circuitConverter = CachingSPCToCircuitConverter.create(formulaFactory, varRanges, defaultRange, satConfig);

        final SATCheckerFactory satCheckerFactory;

        if (Globals.createSatViewLabels && Globals.DEBUG_MPLUECKER) {
            final Arguments satDumpAguments = new Arguments();
            satDumpAguments.path = "e:\\del\\";
            satCheckerFactory = new SATDumpEngine(satDumpAguments );
        } else {
            satCheckerFactory = new MINISATEngine(new MINISATEngine.Arguments());
        }

        final SatSearch satSearch = SatSearch.create(satCheckerFactory, circuitConverter);

        final Set<? extends Formula<Diophantine>> propVars = new LinkedHashSet<Formula<Diophantine>>();
        aborter.checkAbortion();
        Map<String, BigInteger> searchResult = satSearch.search(diophantineFormula, aborter, propVars);
        aborter.checkAbortion();

        if (searchResult != null) {
            searchResult = this.optimizeSearchResult(abstractInterpretation, varMapping, searchResult, diophantineFormulaFactory,
                diophantineFormula,  aborter, varRanges);

            final LinkedHashMap<IVariable<BigInt>, BigInt> varState =
                new LinkedHashMap<IVariable<BigInt>, BigInt>();

            for (final Map.Entry<String, BigInteger> searchVarResult : searchResult.entrySet()) {
                final IVariable<BigInt> polyVar = varMapping.getRL(searchVarResult.getKey());
                final BigInteger value = this.shiftValue(polyVar, searchVarResult.getValue(), defaultVarRange);

                varState.put(polyVar, BigInt.create(value));
            }

            final Map<ItpfLogVar, Boolean> logState = new LinkedHashMap<ItpfLogVar, Boolean>();

            if (Globals.DEBUG_MPLUECKER) {
                this.traceSolvedConstraints(predefinedMap, abstractInterpretation, constraints, varState);
            }

            return abstractInterpretation.specialize(varState, logState);
        }

        return null;
    }

    private void traceConstraints(final Conjunction<Itpf> constraints) {
        System.err.println("ItpfPolyDiophantineSatSolver CONSTRAINTS");
        for (final Itpf constraint : constraints) {
            System.err.println(constraint);
        }
    }

    private void traceDiophantineFormula(final Formula<Diophantine> diophantineFormula) {
        System.err.println("ItpfPolyDiophantineSatSolver DIOPHANTINE");
        System.err.println(diophantineFormula);
    }

    private void traceSolvedConstraints(final IDPPredefinedMap predefinedMap,
        final PolyInterpretation<BigInt> polyInterpretation,
        final Conjunction<Itpf> constraints,
        final LinkedHashMap<IVariable<BigInt>, BigInt> varState) {
        final LinkedHashMap<PolyVariable<?>, Polynomial<?>> substitutionMap =
            new LinkedHashMap<PolyVariable<?>, Polynomial<?>>();

        final PolyFactory polyFactory = polyInterpretation.getFactory();

        for (final Map.Entry<IVariable<BigInt>, BigInt> varStateEntry : varState.entrySet()) {
            substitutionMap.put(varStateEntry.getKey(), polyFactory.create(varStateEntry.getValue()));
        }

        final PolyTermSubstitution substitution = PolyToPolyTermSubstitution.create(
            PolySubstitution.create(ImmutableCreator.create(substitutionMap), true),
            predefinedMap,
            polyInterpretation);

        for (final Itpf constraint : constraints) {
            System.err.println("constraint: " + constraint);
            System.err.println("solved: " + constraint.applySubstitution(substitution, true));
        }

    }

    private Map<String, BigInteger> optimizeSearchResult(final PolyInterpretation<BigInt> abstractInterpretation,
        final BidirectionalMap<IVariable<BigInt>, String> varMapping,
        final Map<String, BigInteger> searchResult,
        final FormulaFactory<Diophantine> diophantineFormulaFactory,
        final Formula<Diophantine> diophantineFormula,
        final Abortion aborter, final Map<String, BigInteger> varRanges) throws AbortionException {

        final Set<ItpfBoolPolyVar<BigInt>> strictVariables = abstractInterpretation.getUsedBooleanPolyVars(ConstantType.StrictOrientation);
        final Set<ItpfBoolPolyVar<BigInt>> boundVariables = abstractInterpretation.getUsedBooleanPolyVars(ConstantType.BoundOrientation);

        final LinkedHashSet<ItpfBoolPolyVar<BigInt>> variablesToOptimize =
            new LinkedHashSet<ItpfBoolPolyVar<BigInt>>(strictVariables);
        variablesToOptimize.addAll(boundVariables);

        final PoloSatConfigInfo satConfig = new PoloSatConfigInfo();
        final BigInteger defaultRange = BigInteger.valueOf(4);

        final SATCheckerFactory satCheckerFactory = new SAT4JEngine(new SAT4JEngine.Arguments());

//        final SATCheckerFactory satCheckerFactory = new MINISATEngine(new MINISATEngine.Arguments());

        Map<String, BigInteger> currentSearchResult = searchResult;

        final FreshNameGenerator freshnames = new FreshNameGenerator(varMapping.getRLMap().keySet(), FreshNameGenerator.PROLOG_VARS);

        for (final ItpfBoolPolyVar<BigInt> variableToOptimize : variablesToOptimize) {
            final String varName = varMapping.getLR(variableToOptimize.getPolyVar());
            if (varName != null) {
                if (!BigInteger.ONE.equals(currentSearchResult.get(varName))) {
                    final LinkedHashMap<String, BigInteger> extendedSearchResult =
                        new LinkedHashMap<String, BigInteger>(currentSearchResult);
                    extendedSearchResult.put(varName, BigInteger.ONE);

                    final Formula<Diophantine> convertedFormula = this.replaceDiophantineVariables(diophantineFormulaFactory, diophantineFormula, extendedSearchResult);

                    final Set<? extends Formula<Diophantine>> propVars = new LinkedHashSet<Formula<Diophantine>>();
                    aborter.checkAbortion();

                    final FormulaFactory<None> formulaFactory = new FullSharingFactory<None>();
                    final CachingSPCToCircuitConverter circuitConverter = CachingSPCToCircuitConverter.create(formulaFactory, varRanges, defaultRange, satConfig);
                    final SatSearch satSearch = SatSearch.create(satCheckerFactory, circuitConverter);
                    final Map<String, BigInteger> remainingSearchResult = satSearch.search(convertedFormula, aborter, propVars);

                    if (remainingSearchResult != null) {
                        currentSearchResult = extendedSearchResult;
                    }
                }
            } else {
                final String freshVarName = freshnames.getFreshName(variableToOptimize.getPolyVar().getName(), false);
                varMapping.putLR(variableToOptimize.getPolyVar(), freshVarName);
                currentSearchResult.put(freshVarName, BigInteger.ONE);
            }
            aborter.checkAbortion();
        }

        return currentSearchResult;
    }

    private Formula<Diophantine> replaceDiophantineVariables(final FormulaFactory<Diophantine> formulaFactory,
        final Formula<Diophantine> currentFormula,
        final Map<String, BigInteger> substitution) {
        final LinkedHashMap<String, SimplePolynomial> polySubst = new LinkedHashMap<String, SimplePolynomial>();
        for (final Map.Entry<String, BigInteger> substEntry : substitution.entrySet()) {
            polySubst.put(substEntry.getKey(), SimplePolynomial.create(substEntry.getValue()));
        }

        final DiophantineSubstitutor converter =
            new DiophantineSubstitutor(polySubst, formulaFactory);

        final TheoryConverterVisitor<Diophantine, Diophantine> visitor =
            new TheoryConverterVisitor<Diophantine, Diophantine>(formulaFactory,
                converter,
                new LinkedHashMap<Variable<Diophantine>, Variable<Diophantine>>());

        return currentFormula.apply(visitor);
    }

    private Formula<Diophantine> createDiophantineFormula(
        final FormulaFactory<Diophantine> diophantineFormulaFactory,
        final Conjunction<Itpf> constraints,
        final PolyInterpretation<BigInt> abstractInterpretation, final BidirectionalMap<IVariable<BigInt>, String> varMapping, final Map<String, BigInteger> varRanges, final Map<IVariable<BigInt>, SimplePolynomial> varPolys, final SemiRingDomain<BigInt> defaultVarRange, final Abortion aborter) throws AbortionException {
        final List<Formula<Diophantine>> completeFormula = new ArrayList<Formula<Diophantine>>();

        try {
            for (final Itpf formula : constraints) {
                final Formula<Diophantine> transformed =
                    this.buildDiophantineFormula(diophantineFormulaFactory, formula,
                        abstractInterpretation,
                        varMapping,
                        varRanges,
                        varPolys,
                        defaultVarRange);

                completeFormula.add(transformed);
                aborter.checkAbortion();
            }
        } catch (final IlegalFormulaAtomException e) {
            throw new UnsupportedOperationException(e.getMessage());
        } catch (final IllegalPolyVariableException e) {
            throw new UnsupportedOperationException(e.getMessage());
        }

        return diophantineFormulaFactory.buildAnd(completeFormula);
    }

    private Formula<Diophantine> buildDiophantineFormula(
        final FormulaFactory<Diophantine> formulaFactory,
        final Itpf formula,
        final PolyInterpretation<BigInt> abstractInterpretation,
        final BidirectionalMap<IVariable<BigInt>, String> varMapping,
        final Map<String, BigInteger> varRanges,
        final Map<IVariable<BigInt>, SimplePolynomial> varPolys,
        final SemiRingDomain<BigInt> defaultVarRange)
            throws IlegalFormulaAtomException, IllegalPolyVariableException {

        final ArrayList<Formula<Diophantine>> totalFormula = new ArrayList<Formula<Diophantine>>();

        for (final ItpfConjClause conjClause : formula.getClauses()) {
            final ArrayList<Formula<Diophantine>> clauseFormula = new ArrayList<Formula<Diophantine>>();

            for (final Map.Entry<? extends ItpfAtom, Boolean> literal : conjClause.getLiterals().entrySet()) {
                if (literal.getKey().isImplication()) {
                    final ItpfImplication implication = (ItpfImplication) literal.getKey();

                    final Formula<Diophantine> precondition = this.buildDiophantineFormula(formulaFactory, implication.getPrecondition(), abstractInterpretation, varMapping, varRanges, varPolys, defaultVarRange);
                    final Formula<Diophantine> conclusion = this.buildDiophantineFormula(formulaFactory, implication.getConclusion(), abstractInterpretation, varMapping, varRanges, varPolys, defaultVarRange);
                    final Formula<Diophantine> dioImplication = formulaFactory.buildImplication(precondition, conclusion);
                    if (literal.getValue()) {
                        clauseFormula.add(dioImplication);
                    } else {
                        clauseFormula.add(formulaFactory.buildNot(dioImplication));
                    }
                } else if (literal.getKey().isBoolPolyVar()) {
                    final Diophantine diophantine = this.convertPolyVar((ItpfBoolPolyVar<BigInt>) literal.getKey(), literal.getValue(), varMapping, varRanges, varPolys, abstractInterpretation.getBoolRange());
                    clauseFormula.add(formulaFactory.buildTheoryAtom(diophantine));
                } else {
                    if (!literal.getKey().isPoly()) {
                        throw new IlegalFormulaAtomException(
                            "illegal atom, only positive poly atoms allowed: "
                                + literal.getKey());
                    }

                    final ItpfPolyAtom<BigInt> polyAtom =
                        (ItpfPolyAtom<BigInt>) literal.getKey();
                    final SimplePolynomial convertedPoly =
                        this.convertPolynomial(polyAtom.getPoly(), abstractInterpretation, varMapping, varRanges, varPolys, defaultVarRange);

                    final Diophantine diophantine = Diophantine.create(convertedPoly, this.getConstraintType(polyAtom.getConstraintType()));
                    if (literal.getValue()) {
                        clauseFormula.add(formulaFactory.buildTheoryAtom(diophantine));
                    } else {
                        clauseFormula.add(formulaFactory.buildNot(formulaFactory.buildTheoryAtom(diophantine)));
                    }
                }
            }

            totalFormula.add(formulaFactory.buildAnd(clauseFormula));
        }

        return formulaFactory.buildOr(totalFormula);
    }

    private ConstraintType getConstraintType(final aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.ConstraintType constraintType) {
        switch (constraintType) {
        case EQ : return ConstraintType.EQ;
        case GE : return ConstraintType.GE;
        case GT : return ConstraintType.GT;
        default: throw new UnsupportedOperationException("unknown constraint type: " + constraintType);
        }
    }

    private SimplePolynomial convertPolynomial(final Polynomial<BigInt> poly,
        final PolyInterpretation<BigInt> abstractInterpretation, final BidirectionalMap<IVariable<BigInt>, String> varMapping, final Map<String, BigInteger> varRanges, final Map<IVariable<BigInt>, SimplePolynomial> varPolys, final SemiRingDomain<BigInt> defaultVarRange)
            throws IllegalPolyVariableException {
        SimplePolynomial res = SimplePolynomial.ZERO;

        for (final Map.Entry<Monomial<BigInt>, BigInt> monomialCoeff : poly.getMonomials().entrySet()) {
            SimplePolynomial monomialPoly =
                SimplePolynomial.create(monomialCoeff.getValue().getBigInt().intValue());

            for (final Map.Entry<? extends PolyVariable<BigInt>, BigInt> exponent : monomialCoeff.getKey().getExponents().entrySet()) {
                if (exponent.getKey().isMax()) {
                    throw new IllegalPolyVariableException(
                        "illegal max poly variable, only real variables allowed: "
                            + exponent.getKey());
                }

                final IVariable<BigInt> realVariable =
                    (IVariable<BigInt>) exponent.getKey();

                if (!abstractInterpretation.isExistQuantified(realVariable)) {
                    throw new IllegalPolyVariableException(
                        "illegal universaly quantified variable: "
                            + exponent.getKey());
                }

                final SimplePolynomial varPoly =
                    this.getVarPoly(realVariable, varMapping, varRanges, varPolys, defaultVarRange);

                monomialPoly = monomialPoly.times(varPoly);
            }

            res = res.plus(monomialPoly);
        }
        return res;
    }

    private Diophantine convertPolyVar(final ItpfBoolPolyVar<BigInt> var, final boolean positive, final BidirectionalMap<IVariable<BigInt>, String> varMapping, final Map<String, BigInteger> varRanges, final Map<IVariable<BigInt>, SimplePolynomial> varPolys, final SemiRingDomain<BigInt> defaultVarRange) {
        final SimplePolynomial varPoly = this.getVarPoly(var.getPolyVar(), varMapping, varRanges, varPolys, defaultVarRange);

        if (positive) {
            return Diophantine.create(varPoly, SimplePolynomial.ONE, ConstraintType.EQ);
        } else {
            return Diophantine.create(varPoly, SimplePolynomial.ZERO, ConstraintType.EQ);
        }
    }


    private SimplePolynomial getVarPoly(final IVariable<BigInt> variable,
        final BidirectionalMap<IVariable<BigInt>, String> varMapping,
        final Map<String, BigInteger> varRanges,
        final Map<IVariable<BigInt>, SimplePolynomial> varPolys, final SemiRingDomain<BigInt> defaultVarRange) {
        SimplePolynomial result = varPolys.get(variable);

        if (result == null) {
            result = this.createVarPoly(variable, varMapping, varRanges, defaultVarRange);
            varPolys.put(variable, result);
        }

        return result;
    }

    private SimplePolynomial createVarPoly(final IVariable<BigInt> realVariable,
        final BidirectionalMap<IVariable<BigInt>, String> varMapping, final Map<String, BigInteger> varRanges, final SemiRingDomain<BigInt> defaultVarRange) {
        IVariable<BigInt> mappedVar =
            varMapping.getRL(realVariable.getName());

        String simpleVarName;

        if (!realVariable.equals(mappedVar)) {
            if (mappedVar != null) {
                int counter = 0;
                String newName;
                do {
                    newName = realVariable.getName() + "_" + counter;
                    mappedVar = varMapping.getRL(newName);
                    counter ++;
                } while (mappedVar != null && !realVariable.equals(mappedVar));

                if (mappedVar == null) {
                    varMapping.putLR(realVariable, newName);
                }
                simpleVarName = newName;
            } else {
                varMapping.putLR(realVariable, realVariable.getName());
                simpleVarName = realVariable.getName();
            }
        } else {
            simpleVarName = realVariable.getName();
        }

        final Map<IndefinitePart, BigInteger> resultMap = new LinkedHashMap<IndefinitePart, BigInteger>();

        final IndefinitePart varIndefinitePart = IndefinitePart.create(simpleVarName, 1);
        resultMap.put(varIndefinitePart, BigInteger.ONE);

        final SemiRingDomain<BigInt> varRange =
            this.getUsedVarRange(realVariable, defaultVarRange);

        if (varRange.getMin() != null) {
            final BigInt min = varRange.getMin();
            if (!min.isZero()) {
                resultMap.put(IndefinitePart.ONE, min.getBigInt());
            }
            if (varRange.getMax() != null) {
                final BigInteger range = varRange.getMax().getBigInt().subtract(varRange.getMin().getBigInt());
                varRanges.put(simpleVarName, range);
            }
        }

        return SimplePolynomial.create(resultMap);
    }


    private BigInteger shiftValue(final IVariable<BigInt> polyVar,
        final BigInteger value, final SemiRingDomain<BigInt> defaultVarRange) {
        final SemiRingDomain<BigInt> varRange = this.getUsedVarRange(polyVar, defaultVarRange);

        if (varRange.getMin() != null) {
            return value.add(varRange.getMin().getBigInt());
        } else {
            return value;
        }
    }

    private SemiRingDomain<BigInt> getUsedVarRange(final IVariable<BigInt> polyVar,
        final SemiRingDomain<BigInt> defaultVarRange) {
        SemiRingDomain<BigInt> varRange = null;

        varRange = polyVar.getDomain();
        if (varRange.getMin() == null && varRange.getMax() == null) {
            varRange = defaultVarRange;
        }

        return varRange;
    }

    private static class IlegalFormulaAtomException extends Exception {

        private static final long serialVersionUID = 1L;

        public IlegalFormulaAtomException(final String message) {
            super(message);
        }
    }

    private static class IllegalPolyVariableException extends Exception {

        private static final long serialVersionUID = 1L;

        public IllegalPolyVariableException(final String message) {
            super(message);
        }
    }

}
