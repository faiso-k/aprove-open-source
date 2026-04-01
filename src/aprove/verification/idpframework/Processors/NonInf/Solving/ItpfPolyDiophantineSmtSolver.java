package aprove.verification.idpframework.Processors.NonInf.Solving;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Polynomials.Interpretation.PolyInterpretation.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author MP
 */
public class ItpfPolyDiophantineSmtSolver implements ItpfPolyConstraintsSolver {

    @Override
    public PolyInterpretation<BigInt> solve(
        final IDPPredefinedMap predefinedMap,
        final PolyInterpretation<BigInt> abstractInterpretation,
        final Conjunction<Itpf> constraints,
        final Abortion aborter) throws AbortionException
    {

        final BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>> varMapping =
            new BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>>();

        final FormulaFactory<SMTLIBTheoryAtom> formulaFactory = new FullSharingFactory<SMTLIBTheoryAtom>();

        final Formula<SMTLIBTheoryAtom> smtFormula =
            this.createSmtFormula(formulaFactory, constraints, abstractInterpretation, varMapping, aborter);

        final Map<String, IVariable<BigInt>> varNames = this.extractVarNames(varMapping);

        if (Globals.DEBUG_MPLUECKER) {
            this.traceConstraints(constraints);
            this.traceSmtFormula(smtFormula);
        }

        final SMTEngine smtEngine = new SMTLIBEngine();
        Pair<YNM, Map<String, String>> r;
        try {
            r = smtEngine.solve(Collections.singletonList(smtFormula), SMTLogic.QF_NIA, aborter);
        } catch (final WrongLogicException e) {
            System.err.println("Solver error: " + e.getErrorMessage());
            r = new Pair<>(YNM.MAYBE, null);
        }

        aborter.checkAbortion();

        if (r.x == YNM.YES) {

            Map<IVariable<BigInt>, BigInt> variableValues = this.extractVariableValues(varNames, r.y);

            variableValues =
                this.optimizeSearchResult(
                    abstractInterpretation,
                    varMapping,
                    varNames,
                    variableValues,
                    formulaFactory,
                    smtEngine,
                    smtFormula,
                    aborter);

            final Map<ItpfLogVar, Boolean> logState = new LinkedHashMap<ItpfLogVar, Boolean>();

            if (Globals.DEBUG_MPLUECKER) {
                this.traceSolvedConstraints(predefinedMap, abstractInterpretation, constraints, variableValues);
            }

            return abstractInterpretation.specialize(variableValues, logState);

        } else {
            return null;
        }
    }

    private Map<String, IVariable<BigInt>> extractVarNames(
        final BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>> varMapping)
    {
        final Map<String, IVariable<BigInt>> varNames = new LinkedHashMap<String, IVariable<BigInt>>();
        for (final Map.Entry<SMTLIBIntVariable, IVariable<BigInt>> varEntry : varMapping.getEntriesLR()) {
            varNames.put(varEntry.getKey().getName(), varEntry.getValue());
        }
        return varNames;
    }

    private LinkedHashMap<IVariable<BigInt>, BigInt> extractVariableValues(
        final Map<String, IVariable<BigInt>> varNames,
        final Map<String, String> smtValues)
    {
        final LinkedHashMap<IVariable<BigInt>, BigInt> result = new LinkedHashMap<IVariable<BigInt>, BigInt>();

        final Set<IVariable<BigInt>> assignedVariables = new HashSet<IVariable<BigInt>>();

        for (final Map.Entry<String, String> smtValue : smtValues.entrySet()) {
            final String varName = smtValue.getKey();
            final IVariable<BigInt> variable = varNames.get(varName);
            assert variable != null;
            assignedVariables.add(variable);
            result.put(variable, BigInt.create(Long.valueOf(smtValue.getValue())));
        }

        assert !assignedVariables.isEmpty() : "missing variable assignments";

        return result;
    }

    private void traceConstraints(final Conjunction<Itpf> constraints) {
        System.err.println("ItpfPolySMTLIBTheoryAtomSatSolver CONSTRAINTS");
        for (final Itpf constraint : constraints) {
            System.err.println(constraint);
        }
    }

    private void traceSmtFormula(final Formula<SMTLIBTheoryAtom> smtFormula) {
        System.err.println("ItpfPolySMTLIBTheoryAtomSatSolver DIOPHANTINE");
        System.err.println(smtFormula);
    }

    private void traceSolvedConstraints(
        final IDPPredefinedMap predefinedMap,
        final PolyInterpretation<BigInt> polyInterpretation,
        final Conjunction<Itpf> constraints,
        final Map<IVariable<BigInt>, BigInt> variableValues)
    {
        final LinkedHashMap<PolyVariable<?>, Polynomial<?>> substitutionMap =
            new LinkedHashMap<PolyVariable<?>, Polynomial<?>>();

        final PolyFactory polyFactory = polyInterpretation.getFactory();

        for (final Map.Entry<IVariable<BigInt>, BigInt> varStateEntry : variableValues.entrySet()) {
            substitutionMap.put(varStateEntry.getKey(), polyFactory.create(varStateEntry.getValue()));
        }

        final PolyTermSubstitution substitution =
            PolyToPolyTermSubstitution.create(
                PolySubstitution.create(ImmutableCreator.create(substitutionMap), true),
                predefinedMap,
                polyInterpretation);

        for (final Itpf constraint : constraints) {
            System.err.println("constraint: " + constraint);
            System.err.println("solved: " + constraint.applySubstitution(substitution, true));
        }

    }

    private Map<IVariable<BigInt>, BigInt> optimizeSearchResult(
        final PolyInterpretation<BigInt> abstractInterpretation,
        final BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>> varMapping,
        final Map<String, IVariable<BigInt>> varNames,
        final Map<IVariable<BigInt>, BigInt> variableValues,
        final FormulaFactory<SMTLIBTheoryAtom> formulaFactory,
        final SMTEngine smtEngine,
        final Formula<SMTLIBTheoryAtom> smtFormula,
        final Abortion aborter) throws AbortionException
    {

        final Set<ItpfBoolPolyVar<BigInt>> strictVariables =
            abstractInterpretation.getUsedBooleanPolyVars(ConstantType.StrictOrientation);
        final Set<ItpfBoolPolyVar<BigInt>> boundVariables =
            abstractInterpretation.getUsedBooleanPolyVars(ConstantType.BoundOrientation);

        final LinkedHashSet<ItpfBoolPolyVar<BigInt>> variablesToOptimize =
            new LinkedHashSet<ItpfBoolPolyVar<BigInt>>(strictVariables);
        variablesToOptimize.addAll(boundVariables);

        Map<IVariable<BigInt>, BigInt> currentSearchResult = variableValues;

        final FreshNameGenerator freshnames =
            new FreshNameGenerator(varMapping.getRLMap().keySet(), FreshNameGenerator.PROLOG_VARS);

        for (final ItpfBoolPolyVar<BigInt> variableToOptimize : variablesToOptimize) {
            if (!BigInteger.ONE.equals(currentSearchResult.get(variableToOptimize.getPolyVar()).getBigInt())) {
                final LinkedHashMap<IVariable<BigInt>, BigInt> extendedSearchResult =
                    new LinkedHashMap<IVariable<BigInt>, BigInt>(currentSearchResult);
                extendedSearchResult.put(variableToOptimize.getPolyVar(), BigInt.ONE);

                final Formula<SMTLIBTheoryAtom> convertedFormula =
                    this.replaceSMTLIBTheoryAtomVariables(formulaFactory, smtFormula, varMapping, extendedSearchResult);

                aborter.checkAbortion();

                Pair<YNM, Map<String, String>> r;
                try {
                    r = smtEngine.solve(Collections.singletonList(convertedFormula), SMTLogic.QF_NIA, aborter);
                } catch (final WrongLogicException e) {
                    System.err.println("Solver error: " + e.getErrorMessage());
                    r = new Pair<>(YNM.MAYBE, null);
                }

                if (r != null && r.x == YNM.YES) {
                    currentSearchResult = extendedSearchResult;
                }
            }
            aborter.checkAbortion();
        }

        return currentSearchResult;
    }

    private Formula<SMTLIBTheoryAtom> replaceSMTLIBTheoryAtomVariables(
        final FormulaFactory<SMTLIBTheoryAtom> formulaFactory,
        final Formula<SMTLIBTheoryAtom> currentFormula,
        final BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>> varMapping,
        final LinkedHashMap<IVariable<BigInt>, BigInt> extendedSearchResult)
    {
        final Map<SMTLIBVariable<?>, SMTLIBValue> smtVarSubst = new LinkedHashMap<SMTLIBVariable<?>, SMTLIBValue>();

        for (final Entry<IVariable<BigInt>, BigInt> substEntry : extendedSearchResult.entrySet()) {
            smtVarSubst.put(
                varMapping.getRL(substEntry.getKey()),
                SMTLIBIntConstant.create(substEntry.getValue().getBigInt()));
        }

        final SMTLIBVarSubstByMapConverter converter = new SMTLIBVarSubstByMapConverter(smtVarSubst, formulaFactory);

        final TheoryConverterVisitor<SMTLIBTheoryAtom, SMTLIBTheoryAtom> visitor =
            new TheoryConverterVisitor<SMTLIBTheoryAtom, SMTLIBTheoryAtom>(
                formulaFactory,
                converter,
                new LinkedHashMap<Variable<SMTLIBTheoryAtom>, Variable<SMTLIBTheoryAtom>>());

        return currentFormula.apply(visitor);
    }

    private Formula<SMTLIBTheoryAtom> createSmtFormula(
        final FormulaFactory<SMTLIBTheoryAtom> formulaFactory,
        final Conjunction<Itpf> constraints,
        final PolyInterpretation<BigInt> abstractInterpretation,
        final BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>> varMapping,
        final Abortion aborter) throws AbortionException
    {
        final List<Formula<SMTLIBTheoryAtom>> completeFormula = new ArrayList<Formula<SMTLIBTheoryAtom>>();

        try {
            for (final Itpf formula : constraints) {
                final Formula<SMTLIBTheoryAtom> transformed =
                    this.buildSMTLIBTheoryAtomFormula(formulaFactory, formula, abstractInterpretation, varMapping);

                completeFormula.add(transformed);
                aborter.checkAbortion();
            }
        } catch (final IlegalFormulaAtomException e) {
            throw new UnsupportedOperationException(e.getMessage());
        } catch (final IllegalPolyVariableException e) {
            throw new UnsupportedOperationException(e.getMessage());
        }

        completeFormula.add(this.getVarRangeConstraints(formulaFactory, varMapping));

        return formulaFactory.buildAnd(completeFormula);
    }

    private Formula<SMTLIBTheoryAtom> getVarRangeConstraints(
        final FormulaFactory<SMTLIBTheoryAtom> formulaFactory,
        final BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>> varMapping)
    {
        final List<SMTLIBTheoryAtom> constraints = new ArrayList<SMTLIBTheoryAtom>();
        for (final Map.Entry<SMTLIBIntVariable, IVariable<BigInt>> entry : varMapping.getEntriesLR()) {
            final SemiRingDomain<BigInt> domain = entry.getValue().getDomain();
            if (domain.getMin() != null) {
                constraints.add(SMTLIBIntGE.create(
                    entry.getKey(),
                    SMTLIBIntConstant.create(domain.getMin().getBigInt())));
            }
            if (domain.getMax() != null) {
                constraints.add(SMTLIBIntGE.create(
                    SMTLIBIntConstant.create(domain.getMax().getBigInt()),
                    entry.getKey()));
            }
        }
        return formulaFactory.buildAnd(formulaFactory.buildTheoryAtoms(constraints));
    }

    private Formula<SMTLIBTheoryAtom> buildSMTLIBTheoryAtomFormula(
        final FormulaFactory<SMTLIBTheoryAtom> formulaFactory,
        final Itpf formula,
        final PolyInterpretation<BigInt> abstractInterpretation,
        final BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>> varMapping)
        throws IlegalFormulaAtomException,
            IllegalPolyVariableException
    {

        final ArrayList<Formula<SMTLIBTheoryAtom>> totalFormula = new ArrayList<Formula<SMTLIBTheoryAtom>>();

        for (final ItpfConjClause conjClause : formula.getClauses()) {
            final ArrayList<Formula<SMTLIBTheoryAtom>> clauseFormula = new ArrayList<Formula<SMTLIBTheoryAtom>>();

            for (final Map.Entry<? extends ItpfAtom, Boolean> literal : conjClause.getLiterals().entrySet()) {
                if (literal.getKey().isImplication()) {
                    final ItpfImplication implication = (ItpfImplication) literal.getKey();

                    final Formula<SMTLIBTheoryAtom> precondition =
                        this.buildSMTLIBTheoryAtomFormula(
                            formulaFactory,
                            implication.getPrecondition(),
                            abstractInterpretation,
                            varMapping);

                    final Formula<SMTLIBTheoryAtom> conclusion =
                        this.buildSMTLIBTheoryAtomFormula(
                            formulaFactory,
                            implication.getConclusion(),
                            abstractInterpretation,
                            varMapping);

                    final Formula<SMTLIBTheoryAtom> dioImplication =
                        formulaFactory.buildImplication(precondition, conclusion);
                    if (literal.getValue()) {
                        clauseFormula.add(dioImplication);
                    } else {
                        clauseFormula.add(formulaFactory.buildNot(dioImplication));
                    }
                } else if (literal.getKey().isBoolPolyVar()) {
                    final SMTLIBTheoryAtom diophantine =
                        this.convertPolyVar((ItpfBoolPolyVar<BigInt>) literal.getKey(), literal.getValue(), varMapping);
                    clauseFormula.add(formulaFactory.buildTheoryAtom(diophantine));
                } else {
                    if (!literal.getKey().isPoly()) {
                        throw new IlegalFormulaAtomException("illegal atom, only positive poly atoms allowed: "
                            + literal.getKey());
                    }

                    final ItpfPolyAtom<BigInt> polyAtom = (ItpfPolyAtom<BigInt>) literal.getKey();
                    final SMTLIBTheoryAtom convertedPoly =
                        this.convertPolynomial(
                            polyAtom.getPoly(),
                            polyAtom.getConstraintType(),
                            abstractInterpretation,
                            varMapping);

                    if (literal.getValue()) {
                        clauseFormula.add(formulaFactory.buildTheoryAtom(convertedPoly));
                    } else {
                        clauseFormula.add(formulaFactory.buildNot(formulaFactory.buildTheoryAtom(convertedPoly)));
                    }
                }
            }

            totalFormula.add(formulaFactory.buildAnd(clauseFormula));
        }

        return formulaFactory.buildOr(totalFormula);
    }

    private SMTLIBTheoryAtom convertPolynomial(
        final Polynomial<BigInt> poly,
        final ConstraintType constraintType,
        final PolyInterpretation<BigInt> abstractInterpretation,
        final BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>> varMapping) throws IllegalPolyVariableException
    {
        final List<SMTLIBIntValue> sum = new ArrayList<SMTLIBIntValue>();

        for (final Map.Entry<Monomial<BigInt>, BigInt> monomialCoeff : poly.getMonomials().entrySet()) {
            final List<SMTLIBIntValue> monomialFactors = new ArrayList<SMTLIBIntValue>();
            monomialFactors.add(SMTLIBIntConstant.create(monomialCoeff.getValue().getBigInt()));

            for (final Map.Entry<? extends PolyVariable<BigInt>, BigInt> exponent : monomialCoeff
                .getKey()
                .getExponents()
                .entrySet())
            {
                if (exponent.getKey().isMax()) {
                    throw new IllegalPolyVariableException("illegal max poly variable, only real variables allowed: "
                        + exponent.getKey());
                }

                final IVariable<BigInt> realVariable = (IVariable<BigInt>) exponent.getKey();

                if (!abstractInterpretation.isExistQuantified(realVariable)) {
                    throw new IllegalPolyVariableException("illegal universaly quantified variable: "
                        + exponent.getKey());
                }

                final SMTLIBIntVariable smtVar = this.getSmtVar(realVariable, varMapping);

                monomialFactors.add(smtVar);
            }

            sum.add(SMTLIBIntMult.create(monomialFactors));
        }

        switch (constraintType) {
        case EQ:
            return SMTLIBIntEquals.create(SMTLIBIntPlus.create(sum), SMTLIBIntConstant.create(BigInteger.ZERO));
        case GE:
            return SMTLIBIntGE.create(SMTLIBIntPlus.create(sum), SMTLIBIntConstant.create(BigInteger.ZERO));
        case GT:
            return SMTLIBIntGT.create(SMTLIBIntPlus.create(sum), SMTLIBIntConstant.create(BigInteger.ZERO));
        default:
            throw new UnsupportedOperationException("unknown constraint type");
        }

    }

    private SMTLIBTheoryAtom convertPolyVar(
        final ItpfBoolPolyVar<BigInt> var,
        final boolean positive,
        final BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>> varMapping)
    {
        final SMTLIBIntVariable smtVar = this.getSmtVar(var.getPolyVar(), varMapping);
        if (positive) {
            return SMTLIBIntEquals.create(smtVar, SMTLIBIntConstant.create(BigInteger.ONE));
        } else {
            return SMTLIBIntEquals.create(smtVar, SMTLIBIntConstant.create(BigInteger.ZERO));
        }
    }

    private SMTLIBIntVariable getSmtVar(
        final IVariable<BigInt> variable,
        final BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>> varMapping)
    {
        SMTLIBIntVariable result = varMapping.getRL(variable);

        if (result == null) {
            result = this.createSmtVar(variable, varMapping);
            varMapping.putRL(variable, result);
        }

        return result;
    }

    private SMTLIBIntVariable createSmtVar(
        final IVariable<BigInt> realVariable,
        final BidirectionalMap<SMTLIBIntVariable, IVariable<BigInt>> varMapping)
    {

        SMTLIBIntVariable result = SMTLIBIntVariable.create(realVariable.getName());

        if (varMapping.containsKeyLR(result) && !realVariable.equals(varMapping.getLR(result))) {
            int counter = 0;
            do {
                final String newName = realVariable.getName() + "_" + counter;
                result = SMTLIBIntVariable.create(newName);
                counter++;
            } while (varMapping.containsKeyLR(result) && !realVariable.equals(varMapping.getLR(result)));
        }

        return result;
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
