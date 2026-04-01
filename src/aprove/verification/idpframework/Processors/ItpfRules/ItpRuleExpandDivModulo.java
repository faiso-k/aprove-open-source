package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.ItpRuleExpandDivModulo.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author MP
 */
/**
 * TODO: fix application mode count
 */
public class ItpRuleExpandDivModulo extends
        AbstractItpfReplaceRule<ModApplicationReplacement, ItpfConjClause, Unused> {

    public ItpRuleExpandDivModulo() {
        super(new ExportableString("[i] ExpandDivModulo"), new ExportableString(
            "[i] ExpandDivModulo"));
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    public boolean isComplete() {
        return true;
    }

    @Override
    public boolean isSound() {
        return true;
    }

    @Override
    public boolean isAtomicMark() {
        return false;
    }

    @Override
    public boolean isClauseMark() {
        return false;
    }

    @Override
    public boolean isContextFree() {
        return true;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return this.equals(mark);
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>> singleton(this);
    }

    @Override
    protected ModApplicationReplacement createContext(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return new ModApplicationReplacement();
    }

    @Override
    protected ExecutionResult<Conjunction<Itpf>, Itpf> postProcess(final IDPProblem idp,
        final ModApplicationReplacement context,
        final ItpfAndWrapper precondition,
        final ExecutionResult<Conjunction<Itpf>, Itpf> result,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        final ItpfFactory itpfFactory = idp.getItpfFactory();
        if (context.isEmpty()) {
            return result;
        }

        final ArrayList<ItpfQuantor> quantification = new ArrayList<ItpfQuantor>();

        for (final DivModSubstitution<?> substitution : context.getMap().values()) {
            quantification.add(itpfFactory.createQuantor(false, substitution.div));
            quantification.add(itpfFactory.createQuantor(false, substitution.mod));
        }

        final ImmutableArrayList<ItpfQuantor> immutableQuantification = ImmutableCreator.create(quantification);

        final ArrayList<Itpf> newResults = new ArrayList<Itpf>();
        for (final Itpf resultFormula : result) {

            // if violated, we must change the code here
            assert resultFormula.getQuantification().isEmpty();

            final Itpf newResult = itpfFactory.create(immutableQuantification, resultFormula.getClauses());

            newResults.add(newResult);
        }

        return new ExecutionResult<Conjunction<Itpf>, Itpf>(
                new Conjunction<Itpf>(ImmutableCreator.create(newResults)),
                result.implication, result.usedApplications, result.fixpointReached);
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause> processLiteral(final IDPProblem idp,
        final ModApplicationReplacement context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter) {

        if (atom.isItp()) {
            final ItpfItp itpAtom = (ItpfItp) atom;
            if (itpAtom.getRelation() == ItpRelation.TO_PLUS) {
                final ITerm<?> l = itpAtom.getL();
                final IFunctionSymbol<BigInt> modFs = (IFunctionSymbol<BigInt>) idp.getPredefinedMap().getFunctionSymbol(Func.Mod, DomainFactory.INTEGER_INTEGER);
                final IFunctionSymbol<BigInt> divFs = (IFunctionSymbol<BigInt>) idp.getPredefinedMap().getFunctionSymbol(Func.Div, DomainFactory.INTEGER_INTEGER);

                final LinkedHashSet<IFunctionSymbol<BigInt>> divAndMod = new LinkedHashSet<IFunctionSymbol<BigInt>>();
                divAndMod.add(modFs);
                divAndMod.add(divFs);

                final Map<IPosition, IFunctionApplication<BigInt>> divModApplications = l.getDeepestFunctionApplication(divAndMod);

                if (!divModApplications.isEmpty()) {
                    final Pair<Itpf, ITerm<?>> newL =
                        this.getReplacedTerm(idp, context, precondition, l, divModApplications, divFs, modFs);

                    final ItpfFactory itpfFactory = idp.getItpfFactory();
                    final ItpfItp newItp = itpfFactory.createItp(newL.y, itpAtom.getKLeft(), itpAtom.getContextL(), ItpRelation.TO_TRANS, itpAtom.getR(), itpAtom.getKRight(), itpAtom.getContextR());

                    final Itpf replacement = itpfFactory.createAnd(newL.x,
                        itpfFactory.create(newItp, true, ITerm.EMPTY_SET));

                    return new ExecutionResult<QuantifiedDisjunction<ItpfConjClause>, ItpfConjClause>(replacement,
                            ImplicationType.EQUIVALENT,
                            ApplicationMode.SingleStep,
                            false);
                }
            }
        }
        return null;
    }

    private Pair<Itpf, ITerm<?>> getReplacedTerm(final IDPProblem idp,
        final ModApplicationReplacement context,
        final ItpfAndWrapper precondition,
        final ITerm<?> l,
        final Map<IPosition, ? extends IFunctionApplication<?>> divModApplications,
        final IFunctionSymbol<BigInt> divFs, final IFunctionSymbol<BigInt> modFs) {
        ITerm<?> newL = l;
        final ItpfFactory itpfFactory = idp.getItpfFactory();

        Itpf condition = itpfFactory.createTrue();

        for (final Map.Entry<IPosition, ? extends IFunctionApplication<?>> divOrModApplication : divModApplications.entrySet()) {
            @SuppressWarnings("rawtypes")
            final IFunctionApplication fa = divOrModApplication.getValue();

            @SuppressWarnings("unchecked")
            final ImmutableTriple<? extends IVariable<?>, ? extends IVariable<?>, Itpf> replacement = this.getDivModSubstitution(idp, context, precondition, fa);

            if (fa.getRootSymbol().equals(divFs)) {
                newL = newL.replaceAt(divOrModApplication.getKey(), replacement.x);
            } else if (fa.getRootSymbol().equals(modFs)) {
                newL = newL.replaceAt(divOrModApplication.getKey(), replacement.y);
            }

            condition = itpfFactory.createAnd(condition, replacement.z);
        }

        return new Pair<Itpf, ITerm<?>>(condition, newL);
    }

    /**
     * @return x: div replacement, y : modReplacement, z: constraint (not quantified)
     */
    private <R extends IntRing<R>> ImmutableTriple<IVariable<R>, IVariable<R>, Itpf> getDivModSubstitution(final IDPProblem idp,
        final ModApplicationReplacement context,
        final ItpfAndWrapper precondition,
        final IFunctionApplication<R> fa) {

        final IDPPredefinedMap predefinedMap = idp.getPredefinedMap();
        final ItpfFactory itpfFactory = idp.getItpfFactory();

        @SuppressWarnings("unchecked")
        final List<? extends IntegerDomain<?>> inputDomains = (List<IntegerDomain<?>>) fa.getRootSymbol().getDomains();
        @SuppressWarnings("unchecked")
        final IntegerDomain<R> inputDomain = (IntegerDomain<R>) inputDomains.get(0);

        final ITerm<?> q = fa.getArgument(1);
        final IFunctionSymbol<?> gtFs = predefinedMap.getFunctionSymbol(Func.Gt, inputDomains);

        final IFunctionSymbol<R> zeroFs = predefinedMap.getIntSym(inputDomain.getRing().zero(), inputDomain);
        final IFunctionApplication<?> zero = ITerm.createFunctionApplication(zeroFs);

        final ITerm<?> TRUE = predefinedMap.getBoolean(true).getTerm();
        final ItpfItp qGt0 = this.createItp(itpfFactory, ITerm.createFunctionApplication(gtFs, q, zero), TRUE);
        final ItpfItp qLt0 = this.createItp(itpfFactory, ITerm.createFunctionApplication(gtFs, zero, q), TRUE);

        @SuppressWarnings("unchecked") DivModSubstitution<R> substitution = (DivModSubstitution<R>) context.getSubstitution(fa.getArguments());

        if (substitution == null) {
            if (Globals.useAssertions) {
                @SuppressWarnings("unchecked")
                final Func func = ((PredefinedFunction<?, R>)fa.getRootSymbol().getSemantics()).getFunc();
                assert func == Func.Mod || func == Func.Div : "semantics must be div or modulo but is" + func;
            }
            final String modSubstitutionVarName = idp.getIdpGraph().getFreshVarGenerator().getFreshVariableName("mod", false);
            final IVariable<R> modSubstitutionVar = IVariable.create(modSubstitutionVarName, fa.getRootSymbol().getResultDomain());


            final String divSubstitutionVarName = idp.getIdpGraph().getFreshVarGenerator().getFreshVariableName("div", false);
            final IVariable<R> divSubstitutionVar = IVariable.create(divSubstitutionVarName, fa.getRootSymbol().getResultDomain());

            final Set<ITerm<?>> newSTerms = new LinkedHashSet<ITerm<?>>();
            newSTerms.add(divSubstitutionVar);
            newSTerms.add(modSubstitutionVar);
            final ImmutableSet<ITerm<?>> immutableNewSTerms = ImmutableCreator.create(newSTerms);

            // p % q <=> p = div * q + mod && |q| > |mod| && p * q * div >= 0 && p * mod >= 0 && (p > 0 && q > 0 ==> div + mod > 0) && (p < 0 && q > 0 ==> - div - mod > 0) && (p > 0 && q < 0 ==> - div + mod > 0) && (p < 0 && q < 0 ==> div - mod > 0)

            // <=> q > 0 && p = div * q + mod && q > mod && q > -mod &&  p * div >= 0 && p * mod >= 0 && (p > 0 ==> div + mod > 0) && (p < 0 ==> - div - mod > 0)
            //     || q < 0 && p = div * q + mod && -q > mod && -q > -mod &&  p * div <= 0 && p * mod >= 0 && (p > 0 ==> - div + mod > 0) && (p < 0 ==> div - mod > 0)

            // <=> q > 0 && p = div * q + mod && q > mod && q > -mod && p * mod >= 0 && (p >= 0 && div >= 0 || p <= 0 && div <= 0)
            //     || q < 0 && p = div * q + mod && -q > mod && -q > -mod && p * mod >= 0 && (p >= 0 && div <= 0 || p <= 0 && div >= 0)

            final ITerm<?> p = fa.getArgument(0);

            final IFunctionSymbol<?> equalsFs = predefinedMap.getFunctionSymbol(Func.Eq, inputDomains);
            final IFunctionSymbol<?> mulFs = predefinedMap.getFunctionSymbol(Func.Mul, inputDomains);
            final IFunctionSymbol<?> addFs = predefinedMap.getFunctionSymbol(Func.Add, inputDomains);
            final IFunctionSymbol<?> subFs = predefinedMap.getFunctionSymbol(Func.Sub, inputDomains);
            final IFunctionSymbol<?> unaryMinusFs = predefinedMap.getFunctionSymbol(Func.UnaryMinus, Collections.singletonList(inputDomain));
            final IFunctionSymbol<?> geFs = predefinedMap.getFunctionSymbol(Func.Ge, inputDomains);

            final IFunctionApplication<?> pEquationTerm = ITerm.createFunctionApplication(equalsFs, p,
                ITerm.createFunctionApplication(addFs, ITerm.createFunctionApplication(mulFs, q, divSubstitutionVar), modSubstitutionVar));
            final ItpfItp pEquation = this.createItp(itpfFactory, pEquationTerm, TRUE);

            final IFunctionApplication<?> pTimesSubstitutionGe0Term = ITerm.createFunctionApplication(geFs,
                ITerm.createFunctionApplication(mulFs, p, modSubstitutionVar), zero);
            final ItpfItp pTimesSubstitutionGe0 = this.createItp(itpfFactory, pTimesSubstitutionGe0Term, TRUE);

            final IFunctionApplication<?> negMod = ITerm.createFunctionApplication(unaryMinusFs, modSubstitutionVar);

            final ItpfItp pGt0 = this.createItp(itpfFactory, ITerm.createFunctionApplication(gtFs, p, zero), TRUE);
            final ItpfItp pLt0 = this.createItp(itpfFactory, ITerm.createFunctionApplication(gtFs, zero, p), TRUE);

            // case q >= 0
            final ItpfConjClause qPosCase;
            {
                final IFunctionApplication<?> qGtModTerm = ITerm.createFunctionApplication(gtFs, q, modSubstitutionVar);
                final ItpfItp qGtMod = this.createItp(itpfFactory, qGtModTerm, TRUE);

                final IFunctionApplication<?> qGtNegModTerm = ITerm.createFunctionApplication(gtFs, q, negMod);
                final ItpfItp qGtNegMod = this.createItp(itpfFactory, qGtNegModTerm, TRUE);

                final IFunctionApplication<?> pTimesDivGe0Term = ITerm.createFunctionApplication(
                    geFs,
                    ITerm.createFunctionApplication(
                        mulFs,
                        p,
                        divSubstitutionVar),
                    zero);
                final ItpfItp pTimesDivGe0 = this.createItp(itpfFactory, pTimesDivGe0Term, TRUE);

                final LiteralMap literals = new LiteralMap();
                literals.put(qGt0, true);
                literals.put(pEquation, true);
                literals.put(qGtMod, true);
                literals.put(qGtNegMod, true);
                literals.put(pTimesDivGe0, true);
                literals.put(pTimesSubstitutionGe0, true);

                // (p > 0 ==> div + mod > 0) && (p < 0 ==> - div - mod > 0)
                final IFunctionApplication<?> divPlusModGt0 = ITerm.createFunctionApplication(
                    gtFs,
                    ITerm.createFunctionApplication(
                        addFs,
                        divSubstitutionVar,
                        modSubstitutionVar),
                    zero);
                literals.put(
                    this.createImplication(
                        itpfFactory,
                        pGt0,
                        this.createItp(itpfFactory, divPlusModGt0, TRUE)),
                    true);

                final IFunctionApplication<?> minusDivMinusModGt0 = ITerm.createFunctionApplication(
                    gtFs,
                    ITerm.createFunctionApplication(
                        subFs,
                        ITerm.createFunctionApplication(unaryMinusFs, divSubstitutionVar),
                        modSubstitutionVar),
                    zero);
                literals.put(
                    this.createImplication(
                        itpfFactory,
                        pLt0,
                        this.createItp(itpfFactory, minusDivMinusModGt0, TRUE)),
                    true);


                qPosCase = itpfFactory.createClause(ImmutableCreator.create(literals), immutableNewSTerms);
            }

            // case 0 > q
            final ItpfConjClause qNegCase;
            {
                final IFunctionApplication<?> negQ = ITerm.createFunctionApplication(unaryMinusFs, q);

                final IFunctionApplication<?> negQGtModTerm = ITerm.createFunctionApplication(gtFs, negQ, modSubstitutionVar);
                final ItpfItp negQGtMod = this.createItp(itpfFactory, negQGtModTerm, TRUE);

                final IFunctionApplication<?> negQGtNegModTerm = ITerm.createFunctionApplication(gtFs, negQ, negMod);
                final ItpfItp negQGtNegMod = this.createItp(itpfFactory, negQGtNegModTerm, TRUE);

                final IFunctionApplication<?> pTimesDivLe0Term = ITerm.createFunctionApplication(
                    geFs,
                    ITerm.createFunctionApplication(
                        mulFs,
                        p,
                        divSubstitutionVar),
                    zero);
                final ItpfItp pTimesDivLe0 = this.createItp(itpfFactory, pTimesDivLe0Term, TRUE);

                final LiteralMap literals = new LiteralMap();
                literals.put(qLt0, true);
                literals.put(pEquation, true);
                literals.put(negQGtMod, true);
                literals.put(negQGtNegMod, true);
                literals.put(pTimesDivLe0, true);
                literals.put(pTimesSubstitutionGe0, true);

                // (p > 0 ==> - div + mod > 0) && (p < 0 ==> div - mod > 0)
                final IFunctionApplication<?> modMinusDivGt0 = ITerm.createFunctionApplication(
                    gtFs,
                    ITerm.createFunctionApplication(
                        subFs,
                        divSubstitutionVar,
                        modSubstitutionVar),
                    zero);
                literals.put(
                    this.createImplication(
                        itpfFactory,
                        pGt0,
                        this.createItp(itpfFactory, modMinusDivGt0, TRUE)),
                    true);

                final IFunctionApplication<?> divMinusModGt0 = ITerm.createFunctionApplication(
                    gtFs,
                    ITerm.createFunctionApplication(
                        subFs,
                        divSubstitutionVar,
                        modSubstitutionVar),
                    zero);
                literals.put(
                    this.createImplication(
                        itpfFactory,
                        pLt0,
                        this.createItp(itpfFactory, divMinusModGt0, TRUE)),
                    true);

                qNegCase = itpfFactory.createClause(ImmutableCreator.create(literals), immutableNewSTerms);
            }

            final Itpf qPosCaseItpf = itpfFactory.create(qPosCase);
            final Itpf qNegCaseItpf = itpfFactory.create(qNegCase);
            final Itpf qWildCaseItpf = itpfFactory.create(qPosCase, qNegCase);

            substitution = context.addSubstitution(fa.getArguments(), divSubstitutionVar, modSubstitutionVar, qPosCaseItpf, qNegCaseItpf, qWildCaseItpf);
        }

        final Signum qSignum = this.searchQSignum(idp.getPolyInterpretation(), precondition, q, qGt0, qLt0);

        if (qSignum.isPos()) {
            return new ImmutableTriple<IVariable<R>, IVariable<R>, Itpf>(substitution.div, substitution.mod, substitution.conditionCaseQGt0);
        } else if (qSignum.isNeg()) {
            return new ImmutableTriple<IVariable<R>, IVariable<R>, Itpf>(substitution.div, substitution.mod, substitution.conditionCaseQLt0);
        } else {
            return new ImmutableTriple<IVariable<R>, IVariable<R>, Itpf>(substitution.div, substitution.mod, substitution.conditionCaseQWild);
        }
    }

    private Signum searchQSignum(final PolyInterpretation<?> polyInterpretation,
        final ItpfAndWrapper precondition,
        final ITerm<?> q, final ItpfItp qGt0, final ItpfItp qLt0) {
        if (q.isVariable()) {
            final IVariable<?> var = (IVariable<?>) q;
            if (!var.getRing().isBoundedRing()) {
                final SemiRing<?> min = var.getDomain().getMin();
                if (min != null && min.signum() >= 0) {
                    return Signum.Pos;
                }

                final SemiRing<?> max = var.getDomain().getMax();
                if (max != null && max.signum() <= 0) {
                    return Signum.Neg;
                }
            }
        }

        final Polynomial<?> qPoly = polyInterpretation.interpretTerm(q, RelDependency.Increasing);
        if (qPoly.isConstant()) {
            return Signum.getSignum(qPoly.getConstantValue().signum());
        }


        for (final QuantifiedDisjunction<ItpfConjClause> prec : precondition.getSingleFormulas()) {
            Signum qSignum = Signum.Unknown;

            for (final ItpfConjClause precondClause : prec.asCollection()) {
                Signum clauseQSignum = Signum.Wild;

                final Boolean gtBoolValue = precondClause.getLiterals().get(qGt0);
                final Boolean ltBoolValue = precondClause.getLiterals().get(qLt0);

                if (gtBoolValue != null) {
                    if (gtBoolValue) {
                        clauseQSignum = Signum.StrictPos;
                    } else {
                        clauseQSignum = Signum.Neg;
                    }
                }

                if (ltBoolValue != null) {
                    if (ltBoolValue) {
                        clauseQSignum = Signum.StrictNeg;
                    } else {
                        clauseQSignum = Signum.Pos;
                    }
                }

                if (qSignum == Signum.Unknown) {
                    qSignum = clauseQSignum;
                } else {
                    qSignum = qSignum.union(clauseQSignum);
                }

                if (qSignum == Signum.Wild) {
                    break;
                }
            }

            if (qSignum.isDetermined()) {
                return qSignum;
            }
        }

        return Signum.Wild;
    }

    private ItpfImplication createImplication(final ItpfFactory itpfFactory,
        final ItpfAtom precondition, final ItpfAtom comclusion) {
        return itpfFactory.createImplication(
            itpfFactory.create(precondition, true, ITerm.EMPTY_SET),
            itpfFactory.create(comclusion, true, ITerm.EMPTY_SET));
    }


    private ItpfItp createItp(final ItpfFactory itpfFactory,
        final IFunctionApplication<?> condition, final ITerm<?> TRUE) {
        return itpfFactory.createItp(condition, null, null, ItpRelation.TO_TRANS, TRUE, null, null);
    }

    protected static class DivModSubstitution<R extends SemiRing<R>> implements Immutable {

        public final IVariable<R> div;
        public final Itpf conditionCaseQGt0;
        public final Itpf conditionCaseQLt0;
        public final Itpf conditionCaseQWild;
        public final IVariable<R> mod;

        public DivModSubstitution(final IVariable<R> div, final IVariable<R> mod,
            final Itpf conditionCaseQGt0, final Itpf conditionCaseQLt0, final Itpf caseQWild) {
                this.div = div;
                this.mod = mod;
                this.conditionCaseQGt0 = conditionCaseQGt0;
                this.conditionCaseQLt0 = conditionCaseQLt0;
                this.conditionCaseQWild = caseQWild;
        }

    }


    protected static class ModApplicationReplacement extends ReplaceContext.ReplaceContextSkeleton {

        private final LinkedHashMap<ImmutableList<ITerm<?>>, DivModSubstitution<?>> map;

        public ModApplicationReplacement() {
            this.map = new LinkedHashMap<ImmutableList<ITerm<?>>, DivModSubstitution<?>>();
        }

        public boolean isEmpty() {
            return this.map.isEmpty();
        }

        public DivModSubstitution<?> getSubstitution(final ImmutableList<ITerm<?>> arguments) {
            return this.map.get(arguments);
        }

        public <R extends SemiRing<R>> DivModSubstitution<R> addSubstitution(final ImmutableList<ITerm<?>> arguments,
            final IVariable<R> divSubstitution,
            final IVariable<R> modSubstitution,
            final Itpf conditionCaseQGt0,
            final Itpf conditionCaseQLt0,
            final Itpf conditionCaseQWild) {
            final DivModSubstitution<R> res = new DivModSubstitution<R>(divSubstitution, modSubstitution, conditionCaseQGt0, conditionCaseQLt0, conditionCaseQWild);
            this.map.put(arguments, res);
            return res;
        }

        public LinkedHashMap<ImmutableList<ITerm<?>>, DivModSubstitution<?>> getMap() {
            return this.map;
        }
    }


    @Override
    protected ItpfConjClause createReplaceData(final ItpfFactory itpfFactory, final LiteralMap conjunction, final ImmutableSet<ITerm<?>> sTerms) {
        return itpfFactory.createClause(ImmutableCreator.create(conjunction), ITerm.EMPTY_SET);
    }
}