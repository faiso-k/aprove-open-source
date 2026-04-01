/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Polynomials.Interpretation;

import java.math.*;
import java.util.*;
import java.util.Map.*;
import java.util.concurrent.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.FreshVarGenerator;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.ShapeHeuristics.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public abstract class PolyInterpretation<C extends SemiRing<C>> extends IDPExportable.IDPExportableSkeleton
    implements
        IDPExportable,
        Exportable
{

    public static enum ConstantType {

        StrictOrientation("bso_"), BoundOrientation("bnd_"), ActiveCondition("ac"), NatDomain("nat");

        private final String prefix;

        ConstantType(final String prefix) {
            this.prefix = prefix;
        }

        public String getPrefix() {
            return this.prefix;
        }
    }

    /**
     * The prefix used for variables that are abstract coefficients.
     */
    public static final String COEFF_PREFIX = "c_";

    /**
     * constants used by ImplRuleConditionalToUnconditional
     */
    public static final String CONDITIONAL_UNCONDITIONAL_P = "p_";
    public static final String CONDITIONAL_UNCONDITIONAL_Q = "q_";

    /**
     * The prefix used for variables that are variables (all-quantified).
     */
    public static final String VARIABLE_PREFIX = "x_";

    public static final String[] CONTEXT_EXTENSION = new String[] {"_dec", "_inc" };

    /**
     * The pgrefix used for variables that will be used for v_f_i.
     */
    public static final String V_f_i_PREFIX = "f_";

    /**
     * The prefix used for the bound constant.
     */
    public static final String BOUND_PREFIX = "BOUND_";

    protected final ConcurrentMap<IFunctionSymbol<?>, ConcurrentMap<Integer, VFISet<C>>> v_f_i;

    protected final ConcurrentMap<ItpfBoolPolyVar<?>, Set<Itpf>> sideConstraints;

    /**
     * Cached IExtendedAfs after specialization
     */
    protected volatile IExtendedAfs extendedAfs;

    private final ConcurrentMap<BooleanPolyVarKey, ConcurrentMap<ConstantType, PolyBooleanVarSwitch<C>>> booleanPolyVars;

    /**
     * context sensitive cache for context sensitive interpretations (div, mod,
     * ...) contains number of possible context decisions + the OrderPoly that
     * represents all of them (switching variable) IFunctionSymbol<?> ->
     * PathToRoot -> Arguments -> (Polynom, quantifications for variables)
     */
    private final ConcurrentMap<IFunctionSymbol<?>, ConcurrentMap<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>>> contextPol;

    private final ConcurrentMap<IFunctionSymbol<?>, Polynomial<C>> pol;

    private final ConcurrentMap<IVariable<?>, IVariable<C>> variableInterpretations;
    private final ConcurrentMap<IVariable<C>, IVariable<?>> reverseVariableInterpretations;

    protected final PolyShapeHeuristic<C> shapeHeuristic;

    protected final PolyFactory factory;

    protected final List<Citation> citations;

    private final SemiRingDomain<C> boolRange;

    private SemiRingDomain<C> coeffRange;

    protected final ItpfFactory constraintFactory;

    private final Set<IVariable<C>> existQuantifications;

    private final ConcurrentMap<IActiveCondition, ActiveSwitchWrapper<C>> activeSwitches;

    private final ActiveSwitchWrapper<C> filteredContextSwitch;

    private ImmutablePair<IVariable<C>, Polynomial<C>> boundConstant;

    protected final C ring;

    protected final FreshVarGenerator freshVarGenerator;

    protected PolyInterpretation(
        final C ring,
        final PolyShapeHeuristic<C> defaultMode,
        final ItpfFactory constraintFactory,
        final FreshVarGenerator freshVarGenerator,
        final List<Citation> citationsParam)
    {
        // System.err.println("COEFF RANGE: " + coeffRange.getList().get(0).x + " - " + coeffRange.getList().get(0).y);
        this.ring = ring;
        this.freshVarGenerator = freshVarGenerator;
        this.factory = constraintFactory.getPolyFactory();
        this.constraintFactory = constraintFactory;
        this.boolRange = ring.createVarRange(ring.zero(), ring.one());

        this.existQuantifications = Collection_Util.<IVariable<C>>createConcurrentHashSet();

        this.shapeHeuristic = defaultMode;
        this.citations = citationsParam;

        this.v_f_i = new ConcurrentHashMap<IFunctionSymbol<?>, ConcurrentMap<Integer, VFISet<C>>>();

        this.sideConstraints = new ConcurrentHashMap<ItpfBoolPolyVar<?>, Set<Itpf>>();

        // initialize boolConstants
        this.booleanPolyVars =
            new ConcurrentHashMap<BooleanPolyVarKey, ConcurrentMap<ConstantType, PolyBooleanVarSwitch<C>>>();

        this.pol = new ConcurrentHashMap<IFunctionSymbol<?>, Polynomial<C>>();

        this.variableInterpretations = new ConcurrentHashMap<IVariable<?>, IVariable<C>>();
        this.reverseVariableInterpretations = new ConcurrentHashMap<IVariable<C>, IVariable<?>>();

        this.contextPol =
            new ConcurrentHashMap<IFunctionSymbol<?>, ConcurrentMap<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>>>();

        this.activeSwitches = new ConcurrentHashMap<IActiveCondition, ActiveSwitchWrapper<C>>();

        this.filteredContextSwitch = this.createFilteredContextSwitch();

        this.boundConstant = this.createBoundConstant();
    }

    private ImmutablePair<IVariable<C>, Polynomial<C>> createBoundConstant() {
        final IVariable<C> var = this.getNextCoeff(this.ring.createUnknownVarRange());
        final ImmutablePair<IVariable<C>, Polynomial<C>> res =
            new ImmutablePair<IVariable<C>, Polynomial<C>>(var, this.factory.create(var));
        this.setExistQuantification(var);
        return res;
    }

    private ActiveSwitchWrapper<C> createFilteredContextSwitch() {
        final ItpfBoolPolyVar<C> incVar = this.getNextLogVar(ConstantType.ActiveCondition);
        final PolyBooleanVarSwitch<C> incSwitch = new PolyBooleanVarSwitch<C>(this.factory, incVar, this.ring.one());
        this.addVariableConstraint(incVar, incSwitch.getFormula(), false);

        final ItpfBoolPolyVar<C> decVar = this.getNextLogVar(ConstantType.ActiveCondition);
        final PolyBooleanVarSwitch<C> decSwitch = new PolyBooleanVarSwitch<C>(this.factory, decVar, this.ring.one());
        this.addVariableConstraint(decVar, decSwitch.getFormula(), false);

        return new ActiveSwitchWrapper<C>(new PolyContextSwitchPair<C>(incSwitch, decSwitch), false, false);
    }

    public C getRing() {
        return this.ring;
    }

    public SemiRingDomain<C> getBoolRange() {
        return this.boolRange;
    }

    public PolyFactory getFactory() {
        return this.factory;
    }

    public ItpfFactory getConstraintFactory() {
        return this.constraintFactory;
    }

    protected boolean isContextFunction(final IFunctionSymbol<?> fs) {
        if (fs.isPredefinedFunction()) {
            final PredefinedFunction<?, ?> func = (PredefinedFunction<?, ?>) fs.getSemantics();
            return func.getFunc() == Func.Div || func.getFunc() == Func.Mod;
        } else {
            return false;
        }
    }

    public boolean isContextSensitive(final ITerm<?> t) {
        final Set<IFunctionSymbol<?>> funcs = t.getFunctionSymbols();
        for (final IFunctionSymbol<?> func : funcs) {
            if (this.isContextFunction(func)) {
                return true;
            }
        }
        return false;
    }

    public Map<IVariable<?>, IVariable<C>> getVariableInterpretations() {
        return this.variableInterpretations;
    }

    public Map<IVariable<C>, IVariable<?>> getReverseVariableInterpretations() {
        return this.reverseVariableInterpretations;
    }

    /**
     * Interprets a ITerm<?> t with a GPoly, built up using the polynomial
     * interpretations of its function symbols.
     * @param t the ITerm<?> to be interpreted
     * @return the polynomial which corresponds to t in this, and a map which
     * variables have to be all-quantified
     */
    public Polynomial<C> interpretTerm(final ITerm<?> t, final RelDependency k) {
        if (Globals.useAssertions) {
            assert (k != null) : t;
        }
        return this.interpretTerm(t, k, IActiveCondition.EMPTY_CONDITION);
    }

    public Polynomial<C> interpretTerm(
        final ITerm<?> t,
        final RelDependency relDependency,
        final IActiveContext activeContext)
    {
        return this.interpretTerm(t, relDependency, IActiveCondition.create(activeContext));
    }

    public Polynomial<C> interpretTerm(
        final ITerm<?> t,
        RelDependency relDependency,
        final IActiveCondition activeCondition)
    {

        if (relDependency == null) {
            relDependency = RelDependency.Increasing;
        }

        if (Globals.useAssertions) {
            assert (t != null && (t instanceof IFunctionApplication<?>) || (t instanceof IVariable<?>));
            // if other terms should ever be created, the below code
            // needs to be checked
        }

        Polynomial<C> result;
        if (t.isVariable()) { // easy: Variable
            final IVariable<?> v = (IVariable<?>) t;

            if (v.getRing().isSameRing(this.ring)) {
                @SuppressWarnings("unchecked")
                IVariable<C> typedVar = (IVariable<C>) v;
                typedVar = ConcurrentUtil.addToCache(this.variableInterpretations, typedVar, typedVar);
                ConcurrentUtil.addToCache(this.reverseVariableInterpretations, typedVar, typedVar);
                result = this.factory.create(typedVar);
            } else {
                IVariable<C> interpretedVar = IVariable.create(v.getName(), this.ring.createUnknownVarRange());

                interpretedVar = this.freshVarGenerator.getFreshVariable(interpretedVar, false);

                interpretedVar = ConcurrentUtil.addToCache(this.variableInterpretations, v, interpretedVar);
                ConcurrentUtil.addToCache(this.reverseVariableInterpretations, interpretedVar, v);

                result = this.factory.create(interpretedVar);
            }
        } else { // IFunctionApplication<?>
            // compute the interpretations of the arguments of t ...
            // System.err.println("interpretTerm " + t);
            final IFunctionApplication<?> fApp = (IFunctionApplication<?>) t;
            final IFunctionSymbol<?> rootSymbol = fApp.getRootSymbol();
            final ImmutableArrayList<? extends ITerm<?>> args = fApp.getArguments();

            result = this.extend(relDependency, activeCondition, rootSymbol);
            assert (result != null) : "missing abstract interpretation for " + rootSymbol;

            if (!args.isEmpty()) { // fApp is a constant
                final ImmutableSet<? extends IVariable<?>> occuringVars = result.getVariables();
                // x_j |-> poly interpretation of t|_j

                final int size = args.size();

                final Map<PolyVariable<?>, Polynomial<?>> substitution =
                    new LinkedHashMap<PolyVariable<?>, Polynomial<?>>(size);

                final ArrayList<Polynomial<C>> argPolys = new ArrayList<Polynomial<C>>(size);

                for (int i = 0; i < size; ++i) {
                    final PolyVariable<C> argVar = this.getVariableForFunctionSymbolArgument(rootSymbol, i);

                    if (!occuringVars.contains(argVar)) {
                        continue;
                    }

                    final IActiveCondition newActiveCondition = activeCondition.add(IActiveAtom.create(rootSymbol, i));

                    final Polynomial<C> argPoly = this.interpretTerm(args.get(i), relDependency, newActiveCondition);

                    argPolys.add(argPoly);
                    substitution.put(argVar, argPoly);
                }

                // and plug the arg polys into the root poly
                result = result.applySubstitution(PolySubstitution.create(ImmutableCreator.create(substitution), true));
            }
        }
        // System.out.println("InterpretTerm: [" + t + "] = " + factory.wrap(result).exportFlatDeep(fvInner, fvOuter, new PLAIN_Util()));
        // System.out.println("InterpretTerm: [" + t + "] = " + result);
        return result;

    }

    public abstract PolyInterpretation<C> specialize(
        final Map<IVariable<C>, C> state,
        final Map<ItpfLogVar, Boolean> logState);

    protected void applySpecialization(
        final PolyInterpretation<C> specialization,
        final Map<IVariable<C>, C> state,
        final Map<ItpfLogVar, Boolean> logState)
    {

        this.specializePolynomials(specialization, state, logState);
        this.specializeContextPol(specialization, state);

        this.specializeBooleanPolyVars(specialization, state);

        this.specializeActiveSwitches(specialization, state);

        specialization.existQuantifications.addAll(this.existQuantifications);
        specialization.v_f_i.putAll(this.v_f_i);
        specialization.sideConstraints.putAll(this.sideConstraints);
        specialization.variableInterpretations.putAll(this.variableInterpretations);
        specialization.reverseVariableInterpretations.putAll(this.reverseVariableInterpretations);
        C boundValue =  state.get(this.boundConstant.x);
        if (boundValue != null) {
            specialization.boundConstant = new ImmutablePair<>(this.boundConstant.x, this.getFactory().create(boundValue));
        }
    }

    private void specializeContextPol(final PolyInterpretation<C> specialization, final Map<IVariable<C>, C> state) {
        // copy and specialize all context pol
        for (final Entry<IFunctionSymbol<?>, ConcurrentMap<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>>> symbolEntry : this.contextPol
            .entrySet())
        {
            ConcurrentMap<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>> newPathMap =
                new ConcurrentHashMap<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>>();
            newPathMap = ConcurrentUtil.addToCache(specialization.contextPol, symbolEntry.getKey(), newPathMap);

            for (final Entry<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>> pathEntry : symbolEntry
                .getValue()
                .entrySet())
            {
                final Polynomial<C> polynomial = pathEntry.getValue();
                // replace according to state
                final Polynomial<C> substPolynomial = polynomial.applyVarSubstitution(state);
                // TODO: maybe cleanup varRanges?
                newPathMap.put(pathEntry.getKey(), substPolynomial);
            }
        }
    }

    private void specializeActiveSwitches(final PolyInterpretation<C> specialization, final Map<IVariable<C>, C> state)
    {
        // contextSwitchConstants
        for (final Entry<IActiveCondition, ActiveSwitchWrapper<C>> entry : this.activeSwitches.entrySet()) {

            ActiveSwitchWrapper<C> wrapper = entry.getValue().clone();
            wrapper = ConcurrentUtil.addToCache(specialization.activeSwitches, entry.getKey(), wrapper);

            final ItpfBoolPolyVar<C> incVariable = entry.getValue().getContextSwitch().inc.getPolyVariable();
            final ItpfBoolPolyVar<C> decVariable = entry.getValue().getContextSwitch().dec.getPolyVariable();
            final C incValue = state.get(incVariable);
            final C decValue = state.get(decVariable);

            if (incValue != null) {
                wrapper.getContextSwitch().inc.setValue(incValue);
            }

            if (decValue != null) {
                wrapper.getContextSwitch().dec.setValue(decValue);
            }
        }
    }

    private
        void
        specializeBooleanPolyVars(final PolyInterpretation<C> specialization, final Map<IVariable<C>, C> state)
    {
        // boolConstants
        for (final Map.Entry<BooleanPolyVarKey, ConcurrentMap<ConstantType, PolyBooleanVarSwitch<C>>> entry : this.booleanPolyVars
            .entrySet())
        {
            ConcurrentMap<ConstantType, PolyBooleanVarSwitch<C>> constMap =
                new ConcurrentHashMap<ConstantType, PolyBooleanVarSwitch<C>>();

            constMap = ConcurrentUtil.addToCache(specialization.booleanPolyVars, entry.getKey(), constMap);

            for (final Map.Entry<ConstantType, PolyBooleanVarSwitch<C>> constEntry : entry.getValue().entrySet()) {
                final PolyBooleanVarSwitch<C> oldSwitch = constEntry.getValue();
                final C value = state.get(oldSwitch.getPolyVariable().getPolyVar());

                if (Globals.useAssertions) {
                    assert (oldSwitch.getValue() == null || value == null || value.equals(oldSwitch.getValue())) : "invalid specialization: "
                        + oldSwitch.getPolyVariable()
                        + " "
                        + oldSwitch.getPolyVariable()
                        + " -> "
                        + value;
                }

                constMap.put(constEntry.getKey(), new PolyBooleanVarSwitch<C>(
                    this.factory,
                    oldSwitch.getPolyVariable(),
                    value));
            }

        }
    }

    private void specializePolynomials(
        final PolyInterpretation<C> specialization,
        final Map<IVariable<C>, C> state,
        final Map<ItpfLogVar, Boolean> logState)
    {
        for (final Entry<IFunctionSymbol<?>, Polynomial<C>> entry : this.pol.entrySet()) {
            Polynomial<C> polynomial = entry.getValue();

            polynomial = polynomial.applyVarSubstitution(state);
            final Polynomial<C> putPol = ConcurrentUtil.addToCache(specialization.pol, entry.getKey(), polynomial);
            assert polynomial.equals(putPol) : "polynomial clash";
        }

    }

    /**
     * @param usedVariables should be some hash collection
     * @return side constraints for given variables
     */
    public Map<ItpfBoolPolyVar<?>, Itpf> getSideConstraints(final Collection<? extends IVariable<?>> usedVariables) {

        final LinkedHashSet<IVariable<?>> completeUsedVariables = new LinkedHashSet<IVariable<?>>(usedVariables);
        final Map<ItpfBoolPolyVar<?>, Itpf> constraints = new LinkedHashMap<ItpfBoolPolyVar<?>, Itpf>();

        boolean changedUsedVariables;
        do {
            changedUsedVariables = false;

            final Map<ItpfBoolPolyVar<?>, Itpf> activeConstraints = this.getActiveConstraints(completeUsedVariables);
            constraints.putAll(activeConstraints);
            if (completeUsedVariables.addAll(CollectionUtil.getVariables(activeConstraints.values()))) {
                changedUsedVariables = true;
            } else {

                final Map<ItpfBoolPolyVar<?>, Itpf> natDomains = this.getNatDomainsConstraints(completeUsedVariables);
                constraints.putAll(natDomains);
                if (completeUsedVariables.addAll(CollectionUtil.getVariables(natDomains.values()))) {
                    changedUsedVariables = true;
                } else {
                    for (final Map.Entry<ItpfBoolPolyVar<?>, Set<Itpf>> entry : this.sideConstraints
                        .entrySet())
                    {
                        if (completeUsedVariables.contains(entry.getKey().getPolyVar())
                            && !constraints.containsKey(entry.getKey()))
                        {
                            final Itpf constraint = this.constraintFactory.createAnd(entry.getValue());
                            constraints.put(entry.getKey(), constraint);
                            if (completeUsedVariables.addAll(constraint.getFreeVariables())) {
                                changedUsedVariables = true;
                            }
                        }
                    }
                }
            }
        } while (changedUsedVariables);

        return constraints;
    }

    private Map<ItpfBoolPolyVar<?>, Itpf> getNatDomainsConstraints(final LinkedHashSet<IVariable<?>> usedVariables) {
        final CollectionMap<SemiRingDomain<?>, IFunctionSymbol<?>> sortedFunctionSymbols =
            this.sortFunctionSymbolsByDomain();

        final Map<ItpfBoolPolyVar<?>, Itpf> res = new LinkedHashMap<ItpfBoolPolyVar<?>, Itpf>();

        LinkedHashSet<SemiRingDomain<?>> domainsToEncode = this.searchNatDomainsToEncode(usedVariables);

        final LinkedHashSet<SemiRingDomain<?>> encodedDomains = new LinkedHashSet<SemiRingDomain<?>>();
        while (!domainsToEncode.isEmpty()) {
            final LinkedHashSet<SemiRingDomain<?>> nextEncodingLevel = new LinkedHashSet<SemiRingDomain<?>>();

            for (final SemiRingDomain<?> domain : domainsToEncode) {
                final LiteralMap constraints = new LiteralMap();

                // add VFI_Constraints (-1 is constant)
                if (sortedFunctionSymbols.containsKey(domain)) {
                    for (final IFunctionSymbol<?> fs : sortedFunctionSymbols.get(domain)) {
                        for (int i = fs.getArity() - 1; i >= -1; i--) {
                            constraints.put(this.getV_f_i(fs, i).inc, true);
                        }
                    }
                }

                final Set<SemiRingDomain<?>> natDomainsClosure = new LinkedHashSet<SemiRingDomain<?>>();
                this.collectNatDomainsClosure(domain, sortedFunctionSymbols, natDomainsClosure);
                natDomainsClosure.remove(domain);
                nextEncodingLevel.addAll(natDomainsClosure);

                final PolyBooleanVarSwitch<C> domainNatBoolVar =
                    this.getPolyBooleanVarSwitch(ConstantType.NatDomain, domain, null);

                for (final SemiRingDomain<?> closureDomain : natDomainsClosure) {
                    constraints.put(this.getItpfBooleanPolyVar(ConstantType.NatDomain, closureDomain, null), true);
                }

                final ItpfImplication implication =
                    this.constraintFactory.createImplication(
                        domainNatBoolVar.getFormula(),
                        this.constraintFactory.create(this.constraintFactory.createClause(
                            ImmutableCreator.create(constraints),
                            ITerm.EMPTY_SET)));

                res.put(
                    domainNatBoolVar.getPolyVariable(),
                    this.constraintFactory.create(implication, true, ITerm.EMPTY_SET));
                encodedDomains.add(domain);
            }

            nextEncodingLevel.removeAll(encodedDomains);
            domainsToEncode = nextEncodingLevel;
        }

        return res;
    }

    private LinkedHashSet<SemiRingDomain<?>> searchNatDomainsToEncode(final LinkedHashSet<IVariable<?>> usedVariables) {
        final LinkedHashSet<SemiRingDomain<?>> domainsToEncode = new LinkedHashSet<SemiRingDomain<?>>();

        for (final Map.Entry<BooleanPolyVarKey, ConcurrentMap<ConstantType, PolyBooleanVarSwitch<C>>> boolPolyVarsEntry : this.booleanPolyVars
            .entrySet())
        {
            if (boolPolyVarsEntry.getKey().key instanceof SemiRingDomain) {
                final SemiRingDomain<?> domain = (SemiRingDomain<?>) boolPolyVarsEntry.getKey().key;
                for (final Map.Entry<ConstantType, PolyBooleanVarSwitch<C>> constantEntry : boolPolyVarsEntry
                    .getValue()
                    .entrySet())
                {
                    if (constantEntry.getKey().equals(ConstantType.NatDomain)
                        && usedVariables.contains(constantEntry.getValue().getPolyVariable().getPolyVar()))
                    {
                        domainsToEncode.add(domain);
                    }
                }
            }
        }
        return domainsToEncode;
    }

    private void collectNatDomainsClosure(
        final SemiRingDomain<?> domain,
        final CollectionMap<SemiRingDomain<?>, IFunctionSymbol<?>> sortedFunctionSymbols,
        final Set<SemiRingDomain<?>> closure)
    {
        final Collection<IFunctionSymbol<?>> fsForDomain = sortedFunctionSymbols.get(domain);
        if (fsForDomain != null) {
            for (final IFunctionSymbol<?> fs : fsForDomain) {
                for (final SemiRingDomain<?> argDomain : fs.getDomains()) {
                    if (closure.add(argDomain)) {
                        this.collectNatDomainsClosure(argDomain, sortedFunctionSymbols, closure);
                    }
                }
            }
        }
    }

    private CollectionMap<SemiRingDomain<?>, IFunctionSymbol<?>> sortFunctionSymbolsByDomain() {
        final CollectionMap<SemiRingDomain<?>, IFunctionSymbol<?>> sortedFunctionSymbols =
            new CollectionMap<SemiRingDomain<?>, IFunctionSymbol<?>>();

        for (final IFunctionSymbol<?> fs : this.pol.keySet()) {
            sortedFunctionSymbols.add(fs.getResultDomain(), fs);
        }

        for (final IFunctionSymbol<?> fs : this.contextPol.keySet()) {
            sortedFunctionSymbols.add(fs.getResultDomain(), fs);
        }
        return sortedFunctionSymbols;
    }

    private Map<ItpfBoolPolyVar<?>, Itpf> getActiveConstraints(final Collection<? extends IVariable<?>> usedVariables) {
        final IActiveHierarchy activeHierarchy = new IActiveHierarchy();
        for (final Map.Entry<IActiveCondition, ActiveSwitchWrapper<C>> activeEntry : this.activeSwitches.entrySet()) {
            final ActiveSwitchWrapper<C> activeSwitch = activeEntry.getValue();
            /* FIXME
             * usedVariables.contains(...getPolyVariable()) always returns false
             * How do we really want to compare IVariables with ItpfBoolPolyVar?
             *
             * Also fix the two instances of this problem below.
             */
            /*
            final PolyBooleanVarSwitch<C> inc = activeSwitch.getContextSwitch().inc;
            final PolyBooleanVarSwitch<C> dec = activeSwitch.getContextSwitch().dec;

            if (activeSwitch.isWildContextForbidden() || activeSwitch.isForceEncoding()
                || usedVariables.contains(inc.getPolyVariable()) || usedVariables.contains(dec.getPolyVariable())) {
                activeHierarchy.addActiveCondition(activeEntry.getKey());
            }
            */
            if (activeSwitch.isWildContextForbidden() || activeSwitch.isForceEncoding()) {
                activeHierarchy.addActiveCondition(activeEntry.getKey());
            } else {
                assert (false);
            }
        }

        final Map<Node<IActiveCondition>, ActiveSwitchWrapper<C>> nodeToSwitchMapping =
            this.getActiveNodeToSwitchMapping(activeHierarchy);

        final Map<ItpfBoolPolyVar<?>, Itpf> activeConstraints = new LinkedHashMap<ItpfBoolPolyVar<?>, Itpf>();
        for (final Map.Entry<Node<IActiveCondition>, ActiveSwitchWrapper<C>> nodeSwitch : nodeToSwitchMapping
            .entrySet())
        {
            final Node<IActiveCondition> node = nodeSwitch.getKey();
            final ActiveSwitchWrapper<C> activeSwitch = nodeSwitch.getValue();
            final ImmutablePair<Itpf, Itpf> encoding = this.getActiveEncoding(activeHierarchy, nodeToSwitchMapping, node);

            final PolyBooleanVarSwitch<C> inc = activeSwitch.getContextSwitch().inc;
            final PolyBooleanVarSwitch<C> dec = activeSwitch.getContextSwitch().dec;

            Itpf wildContextForbid;
            if (activeSwitch.isWildContextForbidden()) {
                final Set<ItpfConjClause> clauses = new LinkedHashSet<ItpfConjClause>();
                clauses.add(this.constraintFactory.createClause(inc.getPolyVariable(), true, ITerm.EMPTY_SET));
                clauses.add(this.constraintFactory.createClause(dec.getPolyVariable(), true, ITerm.EMPTY_SET));

                wildContextForbid = this.constraintFactory.create(ImmutableCreator.create(clauses));
            } else {
                wildContextForbid = this.constraintFactory.createTrue();
            }

            // FIXME: see above
            if (activeSwitch.isWildContextForbidden()
                || activeSwitch.isForceEncoding()
                || usedVariables.contains(inc.getPolyVariable()))
            {
                final Itpf incFormula =
                    this.constraintFactory.create(
                        this.constraintFactory.createImplication(inc.getFormula(), encoding.x),
                        true,
                        ITerm.EMPTY_SET);
                activeConstraints.put(
                    inc.getPolyVariable(),
                    this.constraintFactory.createAnd(incFormula, wildContextForbid));
            }

            // FIXME: see above
            if (activeSwitch.isWildContextForbidden()
                || activeSwitch.isForceEncoding()
                || usedVariables.contains(dec.getPolyVariable()))
            {
                final Itpf decFormula =
                    this.constraintFactory.create(
                        this.constraintFactory.createImplication(dec.getFormula(), encoding.y),
                        true,
                        ITerm.EMPTY_SET);
                activeConstraints.put(
                    dec.getPolyVariable(),
                    this.constraintFactory.createAnd(decFormula, wildContextForbid));
            }
        }
        return activeConstraints;
    }

    private Map<Node<IActiveCondition>, ActiveSwitchWrapper<C>> getActiveNodeToSwitchMapping(
        final IActiveHierarchy activeHierarchy)
    {
        final Map<Node<IActiveCondition>, ActiveSwitchWrapper<C>> result =
            new LinkedHashMap<Node<IActiveCondition>, ActiveSwitchWrapper<C>>();

        for (final Node<IActiveCondition> node : activeHierarchy.getNodes()) {
            ActiveSwitchWrapper<C> activeSwitch = this.activeSwitches.get(node.getObject());
            if (activeSwitch == null) {
                activeSwitch = this.getActiveSwitchWrapper(node.getObject(), false, false);
            }
            result.put(node, activeSwitch);
        }

        return result;
    }

    private ImmutablePair<Itpf, Itpf> getActiveEncoding(
        final IActiveHierarchy activeHierarchy,
        final Map<Node<IActiveCondition>, ActiveSwitchWrapper<C>> nodeToSwitchMapping,
        final Node<IActiveCondition> node)
    {
        final List<Node<IActiveCondition>> parents = activeHierarchy.getParents(node);
        IActiveCondition remaining = node.getObject();
        ImmutablePair<Itpf, Itpf> encoding = null;

        // encode parents
        for (final Node<IActiveCondition> parentNode : parents) {
            final IActiveCondition parentCondition = parentNode.getObject();
            if (!parentCondition.isEmpty()) {
                do {
                    encoding =
                        this.iActiveAnd(encoding, this.getActiveEncoding(activeHierarchy, nodeToSwitchMapping, parentNode));
                    remaining = remaining.subtract(parentCondition);
                } while (remaining.containsAll(parentCondition));
            }
        }

        // encode remaining atoms
        for (final Map.Entry<IActiveAtom, Boolean> activeEntry : remaining.getMap().entrySet()) {
            final IActiveAtom atom = activeEntry.getKey();
            final VFISet<C> vfi = this.getV_f_i(atom.fs, atom.pos);
            encoding = this.iActiveAnd(encoding, vfi.getActiveSwitchPair());
        }

        if (encoding == null) {
            encoding =
                new ImmutablePair<Itpf, Itpf>(this.constraintFactory.createTrue(), this.constraintFactory.createFalse());
        }

        return encoding;
    }

    public IFunctionSymbol<?> getContextReplacementSymbol(
        final IFunctionSymbol<?> fs,
        final IActiveCondition activeCondition,
        final RelDependency dependency,
        final IDPProblem idp)
    {

        if (this.extendedAfs != null) {
            RelDependency relDependence = this.extendedAfs.evaluateContext(activeCondition);
            if (relDependence != null) {
                relDependence = relDependence.combine(dependency);

                final FreshNameGenerator freshName =
                    new FreshNameGenerator(idp.getIdpGraph().getFunctionSymbols(), FreshNameGenerator.VARIABLES);

                final IDPPredefinedMap predefinedMap = idp.getPredefinedMap();

                return IFunctionSymbol.changeName(
                    fs,
                    predefinedMap,
                    freshName.getFreshName(fs.getName() + "^" + relDependence.getK(), true));
            } else {
                throw new IllegalArgumentException("No context decision available for this function symbol / context.");
            }
        } else {
            throw new UnsupportedOperationException("Specialie first?");
        }
    }

    public IVariable<C> getVariableForFunctionSymbolArgument(final IFunctionSymbol<?> fs, final int i) {
        final SemiRingDomain<C> domain = this.ring.createUnknownVarRange();
        final IVariable<C> var = this.factory.createVariable(PolyInterpretation.VARIABLE_PREFIX + i, domain);
        return var;
    }

    public IVariable<C> getVariableForFunctionSymbolArgument(final IFunctionSymbol<?> fs,
        final int i, SemiRingDomain<C> domain) {
        final IVariable<C> var =
            this.factory.createVariable(PolyInterpretation.VARIABLE_PREFIX + i, domain);
        return var;
    }

    private <I extends SemiRing<I>> Polynomial<C> extend(
        final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final IFunctionSymbol<I> fs)
    {
        return this.extend(relDependency, activeCondition, fs, this.shapeHeuristic);
    }

    public <I extends SemiRing<I>> Polynomial<C> extend(
        final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final IFunctionSymbol<I> fs,
        final PolyShapeHeuristic<C> form)
    {

        if (this.isContextFunction(fs)) {
            ConcurrentMap<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>> contextMap =
                this.contextPol.get(fs);

            if (contextMap == null) {
                contextMap = new ConcurrentHashMap<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>>();
                contextMap = ConcurrentUtil.addToCache(this.contextPol, fs, contextMap);
            }

            final ImmutablePair<RelDependency, IActiveCondition> key =
                new ImmutablePair<RelDependency, IActiveCondition>(relDependency, activeCondition);

            Polynomial<C> res = contextMap.get(key);

            if (res == null) {
                res = this.getContextPolyFromFunction(relDependency, activeCondition, fs);
                res = ConcurrentUtil.addToCache(contextMap, key, res);
            }

            return res;
        } else {
            Polynomial<C> res = this.pol.get(fs);

            if (res == null) {
                res = this.getPolynomialFromFunction(fs, form);
                res = ConcurrentUtil.addToCache(this.pol, fs, res);
            }

            return res;
        }
    }

    @SuppressWarnings({"rawtypes" })
    protected <I extends SemiRing<I>> Polynomial<C> getPolynomialFromFunction(
        final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<C> form)
    {
        final PredefinedSemantics<?> sem = symbol.getSemantics();
        if (sem != null) {
            if (sem.isConstructor()) {
                if (PredefinedUtil.isInt(symbol, DomainFactory.INTEGERS)) {
                    return this.getPolyInt((IFunctionSymbol) symbol, form);
                } else {
                    final Boolean boolValue = PredefinedUtil.getBoolValue(symbol);
                    if (boolValue != null) {
                        if (boolValue.booleanValue()) {
                            return this.getPolyTrue(symbol, form);
                        } else {
                            return this.getPolyFalse(symbol, form);
                        }
                    }
                }
            } else {
                final PredefinedFunction<?, ?> func = (PredefinedFunction<?, ?>) sem;
                switch (func.getFunc()) {
                case Add:
                    return this.getPolyAdd(symbol, form);
                case Sub:
                    return this.getPolySub(symbol, form);
                case UnaryMinus:
                    return this.getPolyUnaryMinus(symbol, form);
                case Mul:
                    return this.getPolyMul(symbol, form);
                case Ge:
                    return this.getPolyGe(symbol, form);
                case Gt:
                    return this.getPolyGt(symbol, form);
                case Le:
                    return this.getPolyLe(symbol, form);
                case Lt:
                    return this.getPolyLt(symbol, form);
                case Eq:
                    return this.getPolyEq(symbol, form);
                case Land:
                    return this.getPolyLand(symbol, form);
                case Lor:
                    return this.getPolyLor(symbol, form);
                case Lnot:
                    return this.getPolyLnot(symbol, form);
                default:
                }
            }
            throw new IllegalArgumentException("can not interpret predefined function " + symbol);
        } else {
            return this.getPolynomialFromUserDefinedFunction(symbol, form);
        }
    }

    protected <I extends SemiRing<I>> Polynomial<C> getPolynomialFromUserDefinedFunction(
        final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<C> defaultForm)
    {
        final Triple<Polynomial<C>, Map<IVariable<C>, Boolean>, ConcurrentMap<Integer, VFISet<C>>> shape =
            defaultForm.getShape(this, symbol);

        if (shape == null) {
            throw new UnsupportedOperationException("no shape produced for function symbol " + symbol);
        }

        this.v_f_i.put(symbol, shape.z);
        for (final Map.Entry<Integer, VFISet<C>> posVfiSet : shape.z.entrySet()) {
            final VFISet<C> vfiSet = posVfiSet.getValue();
            this.addVariableConstraint(vfiSet.inc, vfiSet.incCondition, true);
            this.addVariableConstraint(vfiSet.dec, vfiSet.decCondition, true);
            this.setExistQuantification(vfiSet.inc.getPolyVar());
            this.setExistQuantification(vfiSet.inc.getPolyVar());
        }

        synchronized (this.existQuantifications) {
            for (final Map.Entry<IVariable<C>, Boolean> quantification : shape.y.entrySet()) {
                if (!quantification.getValue()) {
                    this.existQuantifications.add(quantification.getKey());
                }
            }
        }

        return shape.x;
    }

    protected abstract <R extends SemiRing<R>> RelDependency getPredefinedV_f_i(
        final IFunctionSymbol<R> fs,
        final int argNr);

    protected abstract Polynomial<C> getPolyInt(final IFunctionSymbol<BigInt> symbol, PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyAdd(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolySub(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyUnaryMinus(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyMul(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getContextPolyFromFunction(
        RelDependency relDependency,
        IActiveCondition activeCondition,
        final IFunctionSymbol<I> fs);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyGe(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyGt(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyLe(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyLt(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyEq(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyLand(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyLnot(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyLor(
        final IFunctionSymbol<I> symbol,
        PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyTrue(
        final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<C> form);

    protected abstract <I extends SemiRing<I>> Polynomial<C> getPolyFalse(
        final IFunctionSymbol<I> symbol,
        final PolyShapeHeuristic<C> form);

    /**
     * Creates pair of boolean coeffs that are 1 if function is used at incr.
     * and decreasing positions respectively
     * @param existQuantifications
     * @param pathToRoot
     * @return
     */
    public ImmutablePair<Polynomial<C>, Polynomial<C>> getContextPolySwitchCoeff(
        final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final boolean forbidWild)
    {
        // simple cases
        switch (relDependency) {
        case Independent:
            return new ImmutablePair<Polynomial<C>, Polynomial<C>>(
                this.factory.one(this.ring),
                this.factory.one(this.ring));
        case Wild:
            if (forbidWild) {
                throw new IllegalArgumentException("wild is forbidden");
            }
            return new ImmutablePair<Polynomial<C>, Polynomial<C>>(
                this.factory.zero(this.ring),
                this.factory.zero(this.ring));
        case Increasing:
            if (activeCondition.isEmpty()) {
                return new ImmutablePair<Polynomial<C>, Polynomial<C>>(
                    this.factory.one(this.ring),
                    this.factory.zero(this.ring));
            } else {
                final PolyContextSwitchPair<C> res = this.getIActiveConstraints(activeCondition, true, forbidWild);
                return new ImmutablePair<Polynomial<C>, Polynomial<C>>(res.inc.getPolynomial(), res.dec.getPolynomial());
            }
        case Decreasing:
            if (activeCondition.isEmpty()) {
                return new ImmutablePair<Polynomial<C>, Polynomial<C>>(
                    this.factory.zero(this.ring),
                    this.factory.one(this.ring));
            } else {
                final PolyContextSwitchPair<C> res = this.getIActiveConstraints(activeCondition, true, forbidWild);
                return new ImmutablePair<Polynomial<C>, Polynomial<C>>(res.dec.getPolynomial(), res.inc.getPolynomial());
            }
        default:
            throw new IllegalArgumentException("unknown RelDependency: " + relDependency);
        }
    }

    public boolean isExistQuantified(final IVariable<?> var) {
        synchronized (this.existQuantifications) {
            return this.existQuantifications.contains(var);
        }
    }

    public void setExistQuantification(final IVariable<C> var) {
        synchronized (this.existQuantifications) {
            this.existQuantifications.add(var);
        }
    }

    protected void addVariableConstraint(final ItpfBoolPolyVar<?> variable, final Collection<Itpf> constraints) {
        Set<Itpf> allConstraints = this.sideConstraints.get(variable);
        if (allConstraints == null) {
            allConstraints = Collection_Util.<Itpf>createConcurrentHashSet();
            allConstraints = ConcurrentUtil.addToCache(this.sideConstraints, variable, allConstraints);
        }

        allConstraints.addAll(constraints);
    }

    protected void addVariableConstraint(
        final ItpfBoolPolyVar<?> variable,
        final Itpf constraint,
        final boolean buildImplication)
    {
        Set<Itpf> allConstraints = this.sideConstraints.get(variable);

        if (allConstraints == null) {
            allConstraints = Collection_Util.<Itpf>createConcurrentHashSet();
            allConstraints = ConcurrentUtil.addToCache(this.sideConstraints, variable, allConstraints);
        }
        if (buildImplication) {
            final ItpfImplication implication =
                this.constraintFactory.createImplication(
                    this.constraintFactory.create(variable, true, ITerm.EMPTY_SET),
                    constraint);
            allConstraints.add(this.constraintFactory.create(implication, true, ITerm.EMPTY_SET));
        } else {
            allConstraints.add(constraint);
        }
    }

    /**
     * @return a new logical variable.
     */
    public final ItpfBoolPolyVar<C> getNextLogVar(final ConstantType constantType) {
        return this.getNextLogVar(constantType.prefix);
    }

    /**
     * @return a new logical variable.
     */
    public final ItpfBoolPolyVar<C> getNextLogVar(final String prefix) {
        synchronized (this) {
            final IVariable<C> var = this.getNextCoeff(prefix, this.boolRange);
            return this.constraintFactory.createBoolPolyVar(var, this);
        }
    }

    /**
     * @return a new PolyVariable representing a fresh coeff.
     */
    public IVariable<C> getNextCoeff(final IFunctionSymbol<?> fs, final int argPosition) {
        return this.getNextCoeff(PolyInterpretation.COEFF_PREFIX + fs.getName() + "_" + argPosition, this.ring.createUnknownVarRange());
    };

    /**
     * @return a new PolyVariable representing a fresh coeff.
     */
    public IVariable<C> getNextCoeff(final IFunctionSymbol<?> fs, final int... indices) {
        String name = PolyInterpretation.COEFF_PREFIX + fs.getName();
        int numberOfIndices = indices.length + 1;
        int counter = 1;
        for (int i : indices) {
            if (counter < numberOfIndices) {
                name += "_";
            }
            name += i;
            counter++;
        }
        return this.getNextCoeff(name, this.ring.createUnknownVarRange());
    };

    /**
     * @return a new PolyVariable representing a fresh coeff with range min <= coeff <= max.
     */
    public IVariable<C> getNextCoeff(final IFunctionSymbol<?> fs, final int argPosition, C min, C max) {
        return this.getNextCoeff(PolyInterpretation.COEFF_PREFIX + fs.getName() + "_" + argPosition, this.ring.createVarRange(min, max));
    };

    /**
     * @return a new PolyVariable representing a fresh coeff.
     */
    public IVariable<C> getNextCoeff(final SemiRingDomain<C> range) {
        return this.getNextCoeff(PolyInterpretation.COEFF_PREFIX, range);
    };

    public IVariable<C> getNextBoolCoeff() {
        return this.getNextCoeff(this.boolRange);
    }

    /**
     * @return a new coefficient variable, existentially quantified.
     */
    public final IVariable<C> getNextCoeff(final String prefix, final SemiRingDomain<C> range) {
        synchronized (this) {
            ;
            final IVariable<C> var = this.freshVarGenerator.getFreshVariable(prefix, range, false);
            this.setExistQuantification(var);
            return var;
        }
    }

    public SemiRingDomain<C> getCoeffRange(final C ring) {
        return this.coeffRange;
    }

    /**
     * The returned constraints may neither contain all quantified variables nor
     * negative numbers
     * @param idpQUsableRules
     * @return
     */
    /*
    public Pair<Set<Pair<OrderPolyConstraint<C>, Polynomial<C>>>, OrderPolyConstraint<C>> getUsableRulesConstraintEquations(final IUsableRulesEstimation usableRules,
        final Abortion aborter) throws AbortionException {
        // System.err.println("usableRulesConstraints " + usableRules);
        final Set<OrderPolyConstraint<C>> constraints =
            new LinkedHashSet<OrderPolyConstraint<C>>();
        final Set<Pair<OrderPolyConstraint<C>, Polynomial<C>>> constraintEquations =
            new LinkedHashSet<Pair<OrderPolyConstraint<C>, Polynomial<C>>>();

        for (final Map.Entry<ITerm<?>, Map<ConstantType, Triple<OPCLogVar<C>, Boolean, OrderPolyConstraint<C>>>> termEntry : termLogVars.entrySet()) {
            final ITerm<?> ITerm<?> = termEntry.getKey();
            final Map<ConstantType, Set<OrderPolyConstraint<C>>> constConstraints =
                new LinkedHashMap<ConstantType, Set<OrderPolyConstraint<C>>>();
            for (final Map.Entry<ConstantType, Triple<OPCLogVar<C>, Boolean, OrderPolyConstraint<C>>> constEntry : termEntry.getValue().entrySet()) {
                if (constEntry.getKey().getIncreasing() != null
                    && constEntry.getKey().getCsar() != null) {
                    constConstraints.put(constEntry.getKey(),
                        new LinkedHashSet<OrderPolyConstraint<C>>());
                }
            }
            if (constConstraints.isEmpty()) {
                continue;
            }

            final IdpQUsableRules activeCond =
                usableRules.getActiveConditions(ITerm<?>);
            // System.err.println("Active: "+ ITerm<?>);
            for (final Map.Entry<GeneralizedRule, IActiveCondition> ruleEntry : activeCond.getActive().entrySet()) {
                final PredefinedFunction<?, ?> func =
                    predefinedMap.getPredefinedFunction(ruleEntry.getKey().getLeft().getRootSymbol());
                if (func != null && func.isArithmetic()) {
                    // predefined arithmetic, because we have fixed interpretation
                    if (func.getFunc() != Func.Div
                        && func.getFunc() != Func.Mod) {
                        continue;
                    }
                }
                // System.err.println(ruleEntry.getKey() + " : " + ruleEntry.getValue());
                final ImmutablePair<? extends OrderPolyConstraint<C>, ? extends OrderPolyConstraint<C>> active =
                    getIActiveConstraints(ruleEntry.getValue(), true);
                if (active.x.equals(constraintFactory.createTrue())
                    && active.y.equals(constraintFactory.createTrue())) {
                    continue;
                }
                final GeneralizedRule rule = ruleEntry.getKey();
                for (final Map.Entry<ConstantType, Triple<OPCLogVar<C>, Boolean, OrderPolyConstraint<C>>> constEntry : termEntry.getValue().entrySet()) {
                    if (constEntry.getKey().getIncreasing() == null
                        || constEntry.getKey().getCsar() == null) {
                        // no usable constant
                        continue;
                    }
                    final ConstantType constType = constEntry.getKey();
                    constConstraints.get(constType).add(
                        constraintFactory.createAnd(constraintFactory.createOr(
                            active.y, getLogVarConstant(
                                resolveUsableConstraintType(
                                    constType.getIncreasing(),
                                    constType.getCsar()), rule)),
                            constraintFactory.createOr(active.x,
                                getLogVarConstant(resolveUsableConstraintType(
                                    !constType.getIncreasing(),
                                    constType.getCsar()), rule))));
                }
            }
            // System.err.println("####");
            for (final Map.Entry<ConstantType, Set<OrderPolyConstraint<C>>> constEntry : constConstraints.entrySet()) {
                if (!constEntry.getValue().isEmpty()) {
                    constraints.add(constraintFactory.createOr(
                        constraintFactory.createNot(getLogVarConstant(
                            constEntry.getKey(), ITerm<?>)),
                        constraintFactory.createAnd(constEntry.getValue())));
                }
            }
        }

        // encode active hierarchy
        final Set<ImmutablePair<IFunctionSymbol<?>, Integer>> usedVfis =
            new LinkedHashSet<ImmutablePair<IFunctionSymbol<?>, Integer>>();
        constraintFor: for (final Node<ImmutablePair<ImmutableSet<ImmutablePair<IFunctionSymbol<?>, Integer>>, ImmutablePair<OPCLogVar<C>, OPCLogVar<C>>>> node : activeHierarchy.getNodes()) {
            if (node.getObject().y == null) {
                // root...
                continue;
            }
            final Set<ImmutablePair<IFunctionSymbol<?>, Integer>> remaining =
                new LinkedHashSet<ImmutablePair<IFunctionSymbol<?>, Integer>>(
                    node.getObject().x);
            final Set<ImmutablePair<OPCLogVar<C>, OPCLogVar<C>>> usedPre =
                new LinkedHashSet<ImmutablePair<OPCLogVar<C>, OPCLogVar<C>>>();
            for (final Node<ImmutablePair<ImmutableSet<ImmutablePair<IFunctionSymbol<?>, Integer>>, ImmutablePair<OPCLogVar<C>, OPCLogVar<C>>>> pre : activeHierarchy.getIn(node)) {
                if (remaining.removeAll(pre.getObject().x)) {
                    usedPre.add(pre.getObject().y);
                    if (remaining.isEmpty()) {
                        break;
                    }
                }
            }
            ImmutablePair<? extends OrderPolyConstraint<C>, ? extends OrderPolyConstraint<C>> andConstraint =
                null;
            for (final ImmutablePair<IFunctionSymbol<?>, Integer> fConstraint : remaining) {
                if (predefinedMap.isUndefinedInt(fConstraint.x)) {
                    continue constraintFor;
                }
                usedVfis.add(fConstraint);
                if (andConstraint == null) {
                    andConstraint =
                        getV_f_i(fConstraint.x, fConstraint.y, true);
                } else {
                    andConstraint =
                        iActiveAnd(andConstraint, getV_f_i(fConstraint.x,
                            fConstraint.y, false));
                }
            }
            for (final ImmutablePair<OPCLogVar<C>, OPCLogVar<C>> pre : usedPre) {
                if (andConstraint == null) {
                    andConstraint = pre;
                } else {
                    andConstraint = iActiveAnd(andConstraint, pre);
                }
            }
            if (andConstraint != null) {
                constraints.add(constraintFactory.createOr(
                    constraintFactory.createNot(node.getObject().y.x),
                    andConstraint.x));
                constraints.add(constraintFactory.createOr(
                    constraintFactory.createNot(node.getObject().y.y),
                    andConstraint.y));
            }
        }

        // encode v_f_i hierarchy
        for (final Map.Entry<IFunctionSymbol<?>, Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<C>, OrderPolyConstraint<C>>>>> fs_vfi : v_f_i_Encodings.entrySet()) {
            for (final Map.Entry<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<C>, OrderPolyConstraint<C>>>> i_vfi : fs_vfi.getValue().entrySet()) {
                if (i_vfi.getValue().x
                    || usedVfis.contains(new ImmutablePair<IFunctionSymbol<?>, Integer>(
                        fs_vfi.getKey(), i_vfi.getKey()))) {
                    final ImmutablePair<OrderPolyConstraint<C>, OrderPolyConstraint<C>> vfi =
                        v_f_i.get(fs_vfi.getKey()).get(i_vfi.getKey());
                    constraints.add(constraintFactory.createOr(
                        constraintFactory.createNot(vfi.x),
                        i_vfi.getValue().y.x));
                    constraints.add(constraintFactory.createOr(
                        constraintFactory.createNot(vfi.y),
                        i_vfi.getValue().y.y));
                }
            }
        }

        for (final Map.Entry<GeneralizedRule, Map<ConstantType, Triple<OPCLogVar<C>, Boolean, OrderPolyConstraint<C>>>> ruleEntry : ruleLogVars.entrySet()) {
            // force filtering of relations
            final GeneralizedRule rule = ruleEntry.getKey();
            final IFunctionSymbol<?> lhsRoot = rule.getLeft().getRootSymbol();
            final PredefinedFunction func =
                predefinedMap.getPredefinedFunction(lhsRoot);
            ;
            if (func != null && (func.isRelation())) {
                // relation -> filter
                for (final Map.Entry<ConstantType, Triple<OPCLogVar<C>, Boolean, OrderPolyConstraint<C>>> constEntry : ruleEntry.getValue().entrySet()) {
                    constraints.add(constraintFactory.createNot(constEntry.getValue().z));
                    // System.err.println("*** Force filter: " + constEntry.getValue().x);
                }
            } else if (func != null && func.isArithmetic()) {
                // predefined arithmetic, because we have fixed interpretation
                for (final Map.Entry<ConstantType, Triple<OPCLogVar<C>, Boolean, OrderPolyConstraint<C>>> constEntry : ruleEntry.getValue().entrySet()) {
                    if (constEntry.getKey().getIncreasing() != null
                        && constEntry.getKey().getCsar() != null) {
                        if (predefinedMap.isDivOrMod(lhsRoot)) {
                            switch (constEntry.getKey().total()) {
                            case Wild:
                                constraints.add(constraintFactory.createNot(constEntry.getValue().z));
                                break;
                            case Decreasing:
                                constraints.add(constraintFactory.createNot(constEntry.getValue().z));
                                break;
                            default:
                                constraints.add(constEntry.getValue().z);
                                break;
                            }
                        } else {
                            constraints.add(constEntry.getValue().z);
                            // System.err.println("*** Auto OK: " + constEntry.getValue().x);
                        }
                    }
                }
            } else {
                // everything else
                for (final Map.Entry<ConstantType, Triple<OPCLogVar<C>, Boolean, OrderPolyConstraint<C>>> constEntry : ruleEntry.getValue().entrySet()) {
                    final ConstantType constType = constEntry.getKey();
                    if (constType.getIncreasing() != null
                        && constType.getCsar() != null) {
                        Polynomial<C> usableRule;
                        if (constType.getIncreasing()) {
                            usableRule =
                                factory.minus(interpretTerm(rule.getLeft(),
                                    constType.getCsar()), interpretTerm(
                                    rule.getRight(), constType.getCsar()));
                        } else {
                            usableRule =
                                factory.minus(interpretTerm(rule.getRight(),
                                    constType.getCsar()), interpretTerm(
                                    rule.getLeft(), constType.getCsar()));
                        }
                        final GPolyWithMinMaxExport<C> visitor =
                            new GPolyWithMinMaxExport<C>(fvInner, fvOuter,
                                factory.getFactory());
                        visitor.applyTo(usableRule);
                        // System.err.println(rule + ":" + constEntry.getValue().x + " @ " + constType + " --->>> " + visitor.export(new PLAIN_Util()));
                        constraintEquations.add(new Pair<OrderPolyConstraint<C>, Polynomial<C>>(
                            constraintFactory.createNot(constEntry.getValue().z),
                            usableRule));
                    }
                }
            }
            if (aborter != null) {
                aborter.checkAbortion();
            }
        }

        // System.err.println("contextUsableRulesConstraints " + contextUsableRulesConstraints);
        return new Pair<Set<Pair<OrderPolyConstraint<C>, Polynomial<C>>>, OrderPolyConstraint<C>>(
            constraintEquations, constraintFactory.createAnd(constraints));
    }

    protected ConstantType resolveUsableConstraintType(final boolean increasing,
        final RelDependency csar) {
        if (increasing) {
            switch (csar) {
            case Decreasing:
                return ConstantType.UsableInc_m1;
            case Independent:
                return ConstantType.UsableInc_0;
            case Increasing:
                return ConstantType.UsableInc_1;
            default:
                return ConstantType.UsableInc_2;
            }
        } else {
            switch (csar) {
            case Decreasing:
                return ConstantType.UsableDec_m1;
            case Independent:
                return ConstantType.UsableDec_0;
            case Increasing:
                return ConstantType.UsableDec_1;
            default:
                return ConstantType.UsableDec_2;
            }
        }
    }*/

    /**
     * The returned constraints may neither contain all quantified variables nor
     * negative numbers
     * @return
     */
    /*
    public OrderPolyConstraint<C> getUsableRulesConstraints() {

        return constraintFactory.createAnd(
            constraintFactory.createAnd(usableRulesConstraints),
            constraintFactory.createAnd(contextUsableRulesConstraints));
    }*/

    /**
     * <true iff increasing, true iff decreasing>
     * @param relDependency
     * @param condition
     * @param forbidWild
     * @return
     */
    public PolyContextSwitchPair<C> getIActiveConstraints(
        final IActiveCondition condition,
        final boolean forceEncoding,
        final boolean forbidWild)
    {
        return this.getActiveSwitchWrapper(condition, forceEncoding, forbidWild).getContextSwitch();
    }

    private ActiveSwitchWrapper<C> getActiveSwitchWrapper(
        final IActiveCondition condition,
        final boolean forceEncoding,
        final boolean forbidWild)
    {

        final Itpf TRUE = this.constraintFactory.createTrue();

        for (final Pair<IActiveAtom, Boolean> activeLiteral : condition) {
            final VFISet<C> vfi = this.getV_f_i(activeLiteral.x.fs, activeLiteral.x.pos);
            if (TRUE.equals(vfi.incCondition) && TRUE.equals(vfi.decCondition)) {
                return this.filteredContextSwitch;
            }
        }

        ActiveSwitchWrapper<C> res;

        res = this.activeSwitches.get(condition);

        if (res != null) {
            if (forbidWild) {
                res.forbidWildContext();
            }
            if (forceEncoding) {
                res.forceEncoding();
            }
            return res;
        }

        final ItpfBoolPolyVar<C> incVar = this.getNextLogVar(ConstantType.ActiveCondition);

        final PolyBooleanVarSwitch<C> incSwitch = new PolyBooleanVarSwitch<C>(this.factory, incVar, null);

        final ItpfBoolPolyVar<C> decVar = this.getNextLogVar(ConstantType.ActiveCondition);

        final PolyBooleanVarSwitch<C> decSwitch = new PolyBooleanVarSwitch<C>(this.factory, decVar, null);

        res = new ActiveSwitchWrapper<C>(new PolyContextSwitchPair<C>(incSwitch, decSwitch), forbidWild, forceEncoding);

        this.activeSwitches.put(condition, res);

        //        if (forbidWild) {
        //            final Itpf forbidWildConstraint = constraintFactory.createOr(
        //                constraintFactory.createClause(incVar, true, ITerm.EMPTY_SET),
        //                constraintFactory.createClause(decVar, true, ITerm.EMPTY_SET)
        //            );
        //
        //            usableRulesConstraints.add(forbidWildConstraint);
        //        }

        return res;
    }

    /**
     * Creates a pair of formulas that determine if the interpretation for f is
     * increasing / decreasing / ignoring / wild with respect to its i-th
     * argument
     * @param f the function symbol
     * @param i the position
     * @param relDependency
     * @param activeCondition
     * @param boolRange the boolean range
     * @return a pair of variables, x : increasing, y : decreasing
     */
    public VFISet<C> getV_f_i(final IFunctionSymbol<?> f, final int i) {
        // check cache
        ConcurrentMap<Integer, VFISet<C>> fEntry = this.v_f_i.get(f);
        VFISet<C> res = null;
        if (fEntry == null) {
            fEntry = new ConcurrentHashMap<Integer, VFISet<C>>();
            fEntry = ConcurrentUtil.addToCache(this.v_f_i, f, fEntry);
        } else {
            res = fEntry.get(i);
        }

        if (res != null) {
            return res;
        }

        {
            final RelDependency d = this.getPredefinedV_f_i(f, i);
            if (d != null) {
                switch (d) {
                case Increasing:
                    res =
                        new VFISet<C>(
                            this.createVFILogVar(f, i, true),
                            this.constraintFactory.createTrue(),
                            this.createVFILogVar(f, i, false),
                            this.constraintFactory.createFalse());
                    break;
                case Decreasing:
                    res =
                        new VFISet<C>(
                            this.createVFILogVar(f, i, true),
                            this.constraintFactory.createFalse(),
                            this.createVFILogVar(f, i, false),
                            this.constraintFactory.createTrue());
                    break;
                case Independent:
                    res =
                        new VFISet<C>(
                            this.createVFILogVar(f, i, true),
                            this.constraintFactory.createTrue(),
                            this.createVFILogVar(f, i, false),
                            this.constraintFactory.createTrue());
                    break;
                default:
                    res =
                        new VFISet<C>(
                            this.createVFILogVar(f, i, true),
                            this.constraintFactory.createFalse(),
                            this.createVFILogVar(f, i, false),
                            this.constraintFactory.createFalse());
                }
                ConcurrentUtil.addToCache(fEntry, i, res);
            }
        }

        if (res == null) {

            Itpf incConclusions;
            Itpf decConclusions;
            final Polynomial<C> fPoly = this.extend(RelDependency.Increasing, IActiveCondition.EMPTY_CONDITION, f);

            if (i < 0) {
                final Polynomial<C> constantPart = fPoly.getConstantPart();

                incConclusions =
                    this.constraintFactory.create(
                        this.constraintFactory.createPoly(constantPart, ConstraintType.GE, this),
                        true,
                        ITerm.EMPTY_SET);
                decConclusions =
                    this.constraintFactory.create(
                        this.constraintFactory.createPoly(constantPart.negate(), ConstraintType.GE, this),
                        true,
                        ITerm.EMPTY_SET);
            } else {
                incConclusions = this.constraintFactory.createTrue();
                decConclusions = this.constraintFactory.createTrue();
                // add constraints
                final PolyVariable<C> var = this.getVariableForFunctionSymbolArgument(f, i);

                monomialSearch: for (final Map.Entry<Monomial<C>, C> monomial : fPoly.getMonomials().entrySet()) {
                    final BigInt exponent = monomial.getKey().getExponents().get(var);
                    if (exponent != null) {
                        // var occurs in monomial
                        final BigInteger TWO = BigInteger.valueOf(2);
                        final boolean evenExponent = exponent.getBigInt().mod(TWO).signum() == 0;
                        final Monomial<C> newMonom = monomial.getKey().removeVar(var);
                        for (final PolyVariable<C> otherVar : newMonom.getExponents().keySet()) {
                            if (otherVar.isRealVar() && !this.isExistQuantified((IVariable<?>) otherVar)) {
                                incConclusions = this.constraintFactory.createFalse();
                                decConclusions = this.constraintFactory.createFalse();
                                break monomialSearch;
                            }
                        }
                        if (evenExponent) {
                            final Itpf eqZero =
                                this.constraintFactory.create(
                                    this.constraintFactory.createPoly(
                                        this.factory.create(newMonom, monomial.getValue()),
                                        ConstraintType.EQ,
                                        this),
                                    true,
                                    ITerm.EMPTY_SET);
                            incConclusions = this.constraintFactory.createAnd(incConclusions, eqZero);
                            decConclusions = this.constraintFactory.createAnd(decConclusions, eqZero);
                        } else {
                            incConclusions =
                                this.constraintFactory.createAnd(
                                    incConclusions,
                                    this.constraintFactory.create(
                                        this.constraintFactory.createPoly(
                                            this.factory.create(newMonom, monomial.getValue()),
                                            ConstraintType.GE,
                                            this),
                                        true,
                                        ITerm.EMPTY_SET));
                            decConclusions =
                                this.constraintFactory.createAnd(
                                    decConclusions,
                                    this.constraintFactory.create(
                                        this.constraintFactory.createPoly(
                                            this.factory.create(newMonom, monomial.getValue().negate()),
                                            ConstraintType.GE,
                                            this),
                                        true,
                                        ITerm.EMPTY_SET));
                        }
                    }
                }
            }

            // create variables
            final ItpfBoolPolyVar<C> f_inc = this.createVFILogVar(f, i, true);
            this.setExistQuantification(f_inc.getPolyVar());
            final ItpfBoolPolyVar<C> f_dec = this.createVFILogVar(f, i, false);
            this.setExistQuantification(f_dec.getPolyVar());

            Itpf enc_inc;
            Itpf enc_dec;

            if (!incConclusions.isTrue()) {
                // f_inc > 0 => incConclusions
                enc_inc = incConclusions;
            } else {
                enc_inc = this.constraintFactory.createTrue();
            }

            if (!decConclusions.isTrue()) {
                // f_dec > 0 => decConclusions
                enc_dec = decConclusions;
            } else {
                enc_dec = this.constraintFactory.createTrue();
            }

            res = new VFISet<C>(f_inc, enc_inc, f_dec, enc_dec);
        }

        // add to cache and return
        ConcurrentUtil.addToCache(fEntry, i, res);
        this.addVariableConstraint(res.inc, res.incCondition, true);
        this.addVariableConstraint(res.dec, res.decCondition, true);

        /*
        // System.err.println("getV_f_i " + f + " / " +i + "\n" + constraintFactory.createOr(constraintFactory.createNot(f_inc),
                constraintFactory.createAnd(incConclusions)) + "\n" + constraintFactory.createOr(constraintFactory.createNot(f_dec),
                        constraintFactory.createAnd(decConclusions)));
                       */
        return res;
    }

    protected ItpfBoolPolyVar<C> createVFILogVar(final IFunctionSymbol<?> f, final int i, final boolean increasing) {
        final IVariable<C> polyVar =
            this.factory.createVariable(
                PolyInterpretation.V_f_i_PREFIX + f.getName() + "_" + i + (increasing ? "_inc" : "dec"),
                this.boolRange);
        return this.constraintFactory.createBoolPolyVar(polyVar, this);
    }

    public ImmutablePair<Itpf, Itpf> iActiveAnd(final ImmutablePair<Itpf, Itpf> x, final ImmutablePair<Itpf, Itpf> y) {
        if (x == null) {
            return y;
        } else if (y == null) {
            return x;
        }
        // result.x = x1^x2 v y1^y2 v x1^y1 v x2^y2
        // result.y = x1^x2 v y1^y2 v x1^y2 v x2^y1

        // shared = x1^x2 v y1^y2
        final Itpf shared =
            this.constraintFactory.createOr(
                this.constraintFactory.createAnd(x.x, x.y),
                this.constraintFactory.createAnd(y.x, y.y));

        final Set<Itpf> x_ors = new LinkedHashSet<Itpf>();
        x_ors.add(shared);
        x_ors.add(this.constraintFactory.createAnd(x.x, y.x));
        x_ors.add(this.constraintFactory.createAnd(x.y, y.y));

        final Set<Itpf> y_ors = new LinkedHashSet<Itpf>();
        y_ors.add(shared);
        y_ors.add(this.constraintFactory.createAnd(x.x, y.y));
        y_ors.add(this.constraintFactory.createAnd(x.y, y.x));

        return new ImmutablePair<Itpf, Itpf>(
            this.constraintFactory.createOr(x_ors),
            this.constraintFactory.createOr(y_ors));
    }

    public ImmutablePair<Itpf, Itpf> iActiveOr(final ImmutablePair<Itpf, Itpf> x, final ImmutablePair<Itpf, Itpf> y) {
        // result.x = x1 & y1
        // result.y = x2 & y2

        return new ImmutablePair<Itpf, Itpf>(
            this.constraintFactory.createAnd(x.x, y.x),
            this.constraintFactory.createAnd(x.y, y.y));
    }

    public IVariable<C> getBoundConstant() {
        return this.boundConstant.x;
    }

    public Polynomial<C> getBoundConstantPoly() {
        return this.boundConstant.y;
    }

    public Set<ItpfBoolPolyVar<C>> getUsedBooleanPolyVars(final ConstantType constantType) {
        final Set<ItpfBoolPolyVar<C>> res = new LinkedHashSet<ItpfBoolPolyVar<C>>();

        for (final ConcurrentMap<ConstantType, PolyBooleanVarSwitch<C>> constantMap : this.booleanPolyVars.values()) {
            final PolyBooleanVarSwitch<C> sw = constantMap.get(constantType);
            if (sw != null) {
                res.add(sw.getPolyVariable());
            }
        }

        return res;
    }

    public Map<ItpfBoolPolyVar<C>, C> getUsedBooleanPolyVarValues(final ConstantType constantType) {
        final Map<ItpfBoolPolyVar<C>, C> res = new LinkedHashMap<ItpfBoolPolyVar<C>, C>();

        for (final ConcurrentMap<ConstantType, PolyBooleanVarSwitch<C>> constantMap : this.booleanPolyVars.values()) {
            final PolyBooleanVarSwitch<C> sw = constantMap.get(constantType);
            if (sw != null) {
                res.put(sw.getPolyVariable(), sw.getValue());
            }
        }

        return res;
    }

    public Polynomial<C> getBooleanPolyVar(
        final ConstantType constantType,
        final SemiRingDomain<?> dom,
        final Set<Itpf> sideConstraints)
    {
        return this.getPolyBooleanVarSwitch(constantType, dom, sideConstraints).getPolynomial();
    }

    public ItpfBoolPolyVar<C> getItpfBooleanPolyVar(
        final ConstantType constantType,
        final SemiRingDomain<?> dom,
        final Set<Itpf> sideConstraints)
    {
        return this.getPolyBooleanVarSwitch(constantType, dom, sideConstraints).getPolyVariable();
    }

    private PolyBooleanVarSwitch<C> getPolyBooleanVarSwitch(
        final ConstantType constantType,
        final SemiRingDomain<?> dom,
        final Set<Itpf> sideConstraints)
    {
        return this.getBooleanPolyVarFromObject(new BooleanPolyVarKey(dom, null), constantType, sideConstraints, true);
    }

    public Polynomial<C> getBooleanPolyVar(
        final ConstantType constantType,
        final ITerm<?> t,
        final Set<Itpf> sideConstraints)
    {
        return this.getBooleanPolyVarFromObject(new BooleanPolyVarKey(t, null), constantType, sideConstraints, true)
            .getPolynomial();
    }

    public ItpfBoolPolyVar<C> getItpfBooleanPolyVar(
        final ConstantType constantType,
        final ITerm<?> t,
        final Set<Itpf> sideConstraints)
    {
        return this.getBooleanPolyVarFromObject(new BooleanPolyVarKey(t, null), constantType, sideConstraints, true)
            .getPolyVariable();
    }

    public C getBooleanPolyVarValue(final ConstantType constantType, final ITerm<?> t, final Set<Itpf> sideConstraints)
    {
        final PolyBooleanVarSwitch<C> res =
            this.getBooleanPolyVarFromObject(new BooleanPolyVarKey(t, null), constantType, sideConstraints, true);
        return res != null ? res.getValue() : null;
    }

    public Polynomial<C> getBooleanPolyVar(
        final ConstantType constantType,
        final IEdge edge,
        final Immutable metaData,
        final Set<Itpf> sideConstraints)
    {
        return this.getBooleanPolyVarFromObject(new BooleanPolyVarKey(edge, metaData), constantType, sideConstraints, true)
            .getPolynomial();
    }

    public ItpfBoolPolyVar<C> getItpfBooleanPolyVar(
        final ConstantType constantType,
        final IEdge edge,
        final Immutable metaData,
        final Set<Itpf> sideConstraints)
    {
        return this.getBooleanPolyVarFromObject(new BooleanPolyVarKey(edge, metaData), constantType, sideConstraints, true)
            .getPolyVariable();
    }

    public C getBooleanPolyVarValue(
        final ConstantType constantType,
        final IEdge edge,
        final Immutable metaData,
        final Set<Itpf> sideConstraints)
    {
        final PolyBooleanVarSwitch<C> res =
            this.getBooleanPolyVarFromObject(new BooleanPolyVarKey(edge, metaData), constantType, sideConstraints, true);
        return res != null ? res.getValue() : null;
    }

    public Polynomial<C> getBooleanPolyVar(
        final ConstantType constantType,
        final INode node,
        final Set<Itpf> sideConstraints)
    {
        return this.getBooleanPolyVarFromObject(new BooleanPolyVarKey(node, null), constantType, sideConstraints, true)
            .getPolynomial();
    }

    public ItpfBoolPolyVar<C> getItpfBooleanPolyVar(
        final ConstantType constantType,
        final INode node,
        final Set<Itpf> sideConstraints)
    {
        return this.getBooleanPolyVarFromObject(new BooleanPolyVarKey(node, null), constantType, sideConstraints, true)
            .getPolyVariable();
    }

    public C getBooleanPolyVarValue(final ConstantType constantType, final INode node, final Set<Itpf> sideConstraints)
    {
        final PolyBooleanVarSwitch<C> res =
            this.getBooleanPolyVarFromObject(new BooleanPolyVarKey(node, null), constantType, sideConstraints, true);
        return res != null ? res.getValue() : null;
    }

    private PolyBooleanVarSwitch<C> getBooleanPolyVarFromObject(
        final BooleanPolyVarKey key,
        final ConstantType constantType,
        final Set<Itpf> sideConstraints,
        final boolean createIfMissing)
    {
        // System.err.println("getLogVarConstant " + constantType + " " + t);
        ConcurrentMap<ConstantType, PolyBooleanVarSwitch<C>> constantMap = this.booleanPolyVars.get(key);

        if (constantMap == null) {
            if (!createIfMissing) {
                return null;
            }
            constantMap = new ConcurrentHashMap<ConstantType, PolyBooleanVarSwitch<C>>();
            this.booleanPolyVars.put(key, constantMap);
        }

        PolyBooleanVarSwitch<C> res = constantMap.get(constantType);
        if (res == null) {
            if (!createIfMissing) {
                return null;
            }
            final ItpfBoolPolyVar<C> var =
                this.getNextLogVar("b_" + key.key.getBooleanPolyVarName() + "_" + constantType.getPrefix());
            res = new PolyBooleanVarSwitch<C>(this.factory, var, null);
            constantMap.put(constantType, res);
        }

        if (sideConstraints != null && !sideConstraints.isEmpty()) {
            final ItpfBoolPolyVar<C> var = res.getPolyVariable();
            Set<Itpf> sideConstrs = this.sideConstraints.get(var);
            if (sideConstrs == null) {
                sideConstrs = Collection_Util.<Itpf>createConcurrentHashSet();
                sideConstrs = ConcurrentUtil.addToCache(this.sideConstraints, var, sideConstrs);
            }
            sideConstrs.addAll(sideConstraints);
        }

        return res;
    }

    protected
        ImmutablePair<RelDependency, ImmutableList<ImmutablePair<IFunctionSymbol<?>, Integer>>>
        duplicatePathToRoot(
            final ImmutablePair<RelDependency, ? extends List<ImmutablePair<IFunctionSymbol<?>, Integer>>> kActiveCondition)
    {
        if (kActiveCondition.y instanceof Immutable) {
            return new ImmutablePair<RelDependency, ImmutableList<ImmutablePair<IFunctionSymbol<?>, Integer>>>(
                kActiveCondition.x,
                (ImmutableList<ImmutablePair<IFunctionSymbol<?>, Integer>>) kActiveCondition.y);
        }
        final ArrayList<ImmutablePair<IFunctionSymbol<?>, Integer>> res =
            new ArrayList<ImmutablePair<IFunctionSymbol<?>, Integer>>(kActiveCondition.y);
        return new ImmutablePair<RelDependency, ImmutableList<ImmutablePair<IFunctionSymbol<?>, Integer>>>(
            kActiveCondition.x,
            ImmutableCreator.create(res));
    }

    public static String[] getContextExtensions() {
        return PolyInterpretation.CONTEXT_EXTENSION;
    }

    protected String getDescription(final Export_Util eu) {
        return "Polynomial interpretation over " + this.ring.getDomainSuffix() + eu.cite(Citation.NONINF);
    }

    @Override
    public void export(final StringBuilder sb, final Export_Util o, final VerbosityLevel verbosityLevel) {
        sb.append("Polynomial interpretation over ");

        sb.append(this.ring.getDomainSuffix());

        sb.append(o.cite(this.citations.toArray(new Citation[0])));
        sb.append(":");
        sb.append(o.linebreak());

        final int size = this.pol.size();
        final List<String> rows = new ArrayList<String>(size);

        Map<IFunctionSymbol<?>, Polynomial<C>> sortedPol; // for ordered display
        sortedPol = new TreeMap<IFunctionSymbol<?>, Polynomial<C>>(this.pol);

        for (final Entry<IFunctionSymbol<?>, Polynomial<C>> entry : sortedPol.entrySet()) {
            String row = this.exportPoly(o, entry.getKey(), entry.getValue(), null, null, verbosityLevel);
            // nasty hack for equidistant lines in HTML (and hence the GUI)
            if (o instanceof HTML_Util) {
                row += "<sup>&nbsp;</sup> <sub>&nbsp;</sub>";
            }
            rows.add(row);
        }

        if (!this.contextPol.isEmpty()) {
            rows.add("");
            rows.add("Polynomial Interpretations with Context Sensitive Arithemetic Replacement");
            final StringBuilder legend = new StringBuilder();
            legend.append("POL(ITerm<?>");
            legend.append(o.sup("CSAR-Mode"));
            legend.append(" @ Context)");
            rows.add(legend.toString());
            rows.add("");
            Map<IFunctionSymbol<?>, ConcurrentMap<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>>> sortedContextPol; // for ordered display
            sortedContextPol =
                new TreeMap<IFunctionSymbol<?>, ConcurrentMap<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>>>(
                    this.contextPol);

            for (final Entry<IFunctionSymbol<?>, ConcurrentMap<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>>> entry : sortedContextPol
                .entrySet())
            {
                // FIXME: add sorting (comparator)
                Map<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>> sortedPathMap; // for ordered display
                sortedPathMap =
                    new TreeMap<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>>(
                        new ImmutablePairComparator<RelDependency, IActiveCondition>());
                sortedPathMap.putAll(entry.getValue());

                for (final Entry<ImmutablePair<RelDependency, IActiveCondition>, Polynomial<C>> k_pathEntry : sortedPathMap
                    .entrySet())
                {
                    String row =
                        this.exportPoly(
                            o,
                            entry.getKey(),
                            k_pathEntry.getValue(),
                            k_pathEntry.getKey().x,
                            k_pathEntry.getKey().y,
                            verbosityLevel);
                    // nasty hack for equidistant lines in HTML (and hence the GUI)
                    if (o instanceof HTML_Util) {
                        row += "<sup>&nbsp;</sup> <sub>&nbsp;</sub>";
                    }
                    rows.add(row);
                }
            }
        }

        String row =
                "POL(" + this.boundConstant.x.toString() + ") = " + this.boundConstant.y;

            // nasty hack for equidistant lines in HTML (and hence the GUI)
            if (o instanceof HTML_Util) {
                row += "<sup>&nbsp;</sup> <sub>&nbsp;</sub>";
            }
            rows.add(row);

        sb.append(o.set(rows, Export_Util.RULES));
    }

    private String exportPoly(
        final Export_Util eu,
        final IFunctionSymbol<?> functionSymbol,
        final Polynomial<C> polynomial,
        final RelDependency relDependency,
        final IActiveCondition activeContext,
        final VerbosityLevel verbosityLevel)
    {
        final StringBuilder line = new StringBuilder("POL(");

        final int arity = functionSymbol.getArity();

        final StringBuilder functionWithVars = new StringBuilder(functionSymbol.export(eu));
        if (arity > 0) {
            functionWithVars.append("(");
            for (int i = 0; i < arity; ++i) {
                this.getVariableForFunctionSymbolArgument(functionSymbol, i).export(functionWithVars, eu, verbosityLevel);
                if (i < arity - 1) {
                    functionWithVars.append(", ");
                }
            }
            functionWithVars.append(")");
        }

        line.append(eu.bold(functionWithVars.toString()));
        if (relDependency != null) {
            line.append(eu.sup(relDependency.getK().toString()));
        }
        if (activeContext != null) {
            line.append(" @ ");
            activeContext.export(line, eu, verbosityLevel);
        }
        line.append(") = ");
        // get the string representation of the polynomial where all
        // values are flattened
        line.append(polynomial.export(eu));
        return line.toString();
    }

    /**
     * @author Marcel Klinzing
     */
    public int getMaxDegree(ImmutableSet<IFunctionSymbol<?>> funcSymbols) {
        //Get max degree of the polynomial interpretation
        int degree = 0;
        for (ConcurrentMap.Entry<IFunctionSymbol<?>, ?> polEntry : this.pol.entrySet()) {
            if (funcSymbols.contains(polEntry.getKey())) {
                Polynomial<?> pol = (Polynomial<?>) polEntry.getValue();
                for (Monomial<?> monom : pol.getMonomials().keySet()) {
                    for (BigInt deg : monom.getExponents().values()) {
                        if (deg.intValue() > degree) {
                            degree = deg.intValue();
                        }
                    }
                }
            }

        }
        return degree;
    }
}
