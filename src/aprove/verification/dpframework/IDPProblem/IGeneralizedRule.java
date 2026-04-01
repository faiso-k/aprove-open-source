package aprove.verification.dpframework.IDPProblem;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.Globals.AproveVersion;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.IDPProblem.utility.IDPExport.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * An IDP rewrite rule.
 *
 * An IGeneralizedRule consists of a standard rewrite {@link GeneralizedRule}
 * and an integer condition. The relations (<code>Predicate.Kind</code>) in the
 * integer condition may only be the Int* ones.
 */
// TODO What about the interfaces
// HasFunctionSymbols, HasVariables, and XMLExportable?
public final class IGeneralizedRule
    implements
        Immutable,
        Exportable,
        CPFAdditional,
        HasRootSymbol,
        HasTRSTerms,
        HasVariables,
        HasFunctionSymbols,
        HasLHS,
        HasRuleForm
{

    /** The integer condition of this IGeneralizedRule as Term */
    private final TRSTerm condTerm;

    /** The rewriting rule of this IGeneralizedRule */
    private final GeneralizedRule rule;

    /** The output variables of rule */
    private List<TRSTerm> leftOutputVariables;

    private IGeneralizedRule(final TRSFunctionApplication l, final TRSTerm r, final TRSTerm ct) {
        this.rule = GeneralizedRule.create(l, r);
        this.condTerm = ct;
    }
    private IGeneralizedRule(final TRSFunctionApplication l, final TRSTerm r, final TRSTerm ct, final List<TRSTerm> lOutVars) {
        this.rule = GeneralizedRule.create(l, r);
        this.condTerm = ct;
        this.leftOutputVariables = lOutVars;
    }

    /** Creates a new IGeneralizedRule.
     *
     * @param l Lhs of the rewrite rule
     * @param r Rhs of the rewrite rule
     * @param c Integer condition
     * @return the new rule
     */
    public static IGeneralizedRule create(final TRSFunctionApplication l, final TRSTerm r, final TRSTerm c) {
        return new IGeneralizedRule(l, r, c);
    }
    public static IGeneralizedRule create(final TRSFunctionApplication l, final TRSTerm r, final TRSTerm c, final List<TRSTerm> lOutVars) {
        return new IGeneralizedRule(l, r, c, lOutVars);
    }

    /**
     * Transforms a collection of IGeneralizedRule to a collection of GeneralizedRule.
     *
     * <p>
     * The conditions are preserved by adding new Terms (see CTRS -&lt; QTRS
     * transformation)
     * </p>
     *
     * FIXME: Document what kind of conditions are allowed (see also
     * {@link CTRSToQTRSProcessor})
     */
    public static Set<GeneralizedRule> removeConditions(final Collection<IGeneralizedRule> c) {
        return IGeneralizedRule.removeConditions(c, false);
    }

    /**
     * Transforms a collection of IGeneralizedRule to a collection of GeneralizedRule.
     *
     * <p>
     * The conditions are preserved by adding new Terms (see CTRS -&lt; QTRS
     * transformation)
     * </p>
     *
     * FIXME: Document what kind of conditions are allowed (see also
     * {@link CTRSToQTRSProcessor})
     */
    public static Set<GeneralizedRule> removeConditions(
        final Collection<IGeneralizedRule> c,
        final boolean allowFreeVarsInCond)
    {
        final Set<GeneralizedRule> rules = new LinkedHashSet<GeneralizedRule>();

        final Set<String> used = new LinkedHashSet<String>();
        for (final FunctionSymbol f : CollectionUtils.getFunctionSymbols(c)) {
            used.add(f.getName());
        }
        final FreshNameGenerator fg = new FreshNameGenerator(used, FreshNameGenerator.PROLOG_VARS);

        /* Split the set of integer rules into unconditional and conditional rules and encode conditions */
        for (final IGeneralizedRule i : c) {
            final GeneralizedRule rule = GeneralizedRule.create(i.getLeft(), i.getRight());
            if (i.getCondTerm() == null || i.getCondTerm().equals(PredefinedSemanticsFactory.BOOLEAN_TERM_TRUE)) {
                rules.add(rule);
            } else {
                /* For a rule f(x1 ... xn) -> g(y1 ... ym) :|: cond, generate
                 *  f(x1 ... xn) -> f_COND(cond, x1 ... xn, y_{i_1} ... y_{i_k})
                 *  f_COND(TRUE, y1 ... ym, y_{i_1} ... y_{i_k}) -> g(y1 ... ym)
                 * where y_{i_1} ... y_{i_k} are the fresh variables that do not
                 * occur on the lhs.
                 */
                if (i.getCondTerm().equals(PredefinedSemanticsFactory.BOOLEAN_TERM_FALSE)) {
                    continue;
                }
                final Set<TRSVariable> variables = i.getLeft().getVariables();
                variables.addAll(i.getRight().getVariables());
                if (Globals.useAssertions && !allowFreeVarsInCond) {
                    assert variables.containsAll(i.getCondTerm().getVariables()) : i
                        + " has free variables in conditions";
                }

                final Collection<TRSVariable> freshVars = i.getRight().getVariables();
                freshVars.removeAll(i.getLeft().getVariables());

                final ArrayList<TRSTerm> rightArgs = new ArrayList<TRSTerm>();
                rightArgs.add(i.getCondTerm());
                rightArgs.addAll(i.getLeft().getArguments());
                rightArgs.addAll(freshVars);
                final FunctionSymbol condRoot =
                    FunctionSymbol.create(
                        fg.getFreshName("Cond_" + i.getRootSymbol().getName(), false),
                        rightArgs.size());
                final ArrayList<TRSTerm> leftArgs = new ArrayList<TRSTerm>(rightArgs);
                leftArgs.set(0, PredefinedSemanticsFactory.BOOLEAN_TERM_TRUE);
                final TRSFunctionApplication condRight =
                    TRSTerm.createFunctionApplication(condRoot, ImmutableCreator.create(rightArgs));
                final TRSFunctionApplication condLeft =
                    TRSTerm.createFunctionApplication(condRoot, ImmutableCreator.create(leftArgs));
                rules.add(GeneralizedRule.create(i.getLeft(), condRight));
                rules.add(GeneralizedRule.create(condLeft, i.getRight()));
            }
        }

        return rules;
    }

    private GeneralizedRule toFullGeneralizedRule() {
        TRSTerm right;
        if (this.condTerm == null) {
            FunctionSymbol f = FunctionSymbol.create("1", 1);
            right = TRSFunctionApplication.createFunctionApplication(f, this.rule.getRight());
        } else {
            FunctionSymbol f = FunctionSymbol.create("2", 2);
            right = TRSFunctionApplication.createFunctionApplication(f, this.rule.getRight(), this.condTerm);
        }
        return GeneralizedRule.create(this.rule.getLeft(), right);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final IGeneralizedRule other = (IGeneralizedRule) obj;
        return (this.toFullGeneralizedRule().equals(other.toFullGeneralizedRule()));
    }

    @Override
    public String export(final Export_Util eu) {
        return this.export(eu, null, null, null);
    }

    public String export(
        final Export_Util eu,
        final LinkedHashMap<Position, PositionMarker> lhsMarkers,
        final LinkedHashMap<Position, PositionMarker> rhsMarkers,
        final LinkedHashMap<Position, PositionMarker> condMarkers)
    {
        final StringBuilder s = new StringBuilder();

        Set<TRSVariable> freeVars;
        if (Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION && eu instanceof HTML_Util) {
            freeVars = this.rule.getRight().getVariables();
            freeVars.removeAll(this.rule.getLeft().getVariables());
        } else {
            freeVars = java.util.Collections.<TRSVariable>emptySet();
        }
        final IDPPredefinedMap map = IDPPredefinedMap.DEFAULT_MAP;

        IDPExport.exportTermWithPrec(this.rule.getLeft(), 0, eu, freeVars, map, s, lhsMarkers);
        s.append(" ");
        s.append(eu.rightarrow());
        s.append(" ");
        IDPExport.exportTermWithPrec(this.rule.getRight(), 0, eu, freeVars, map, s, rhsMarkers);
        if (this.condTerm != null) {
            s.append(" :|: ");
            IDPExport.exportTermWithPrec(this.condTerm, 0, eu, freeVars, map, s, condMarkers);
        }

        return s.toString();
    }

    /**
     * Fills up the variables (useful for ITS (KoAT/LoAT))
     * E.g., f(x,y) -> g(x) with and n = 3 yields f(x,y,t1) -> g(x,t2,t3).
     */
    public IGeneralizedRule fillUpVars(FreshNameGenerator fng, int maxVars) {

        TRSFunctionApplication l = rule.getLeft();
        final ArrayList<TRSTerm> leftArgs = new ArrayList<TRSTerm>();
        leftArgs.addAll(l.getArguments());
        for(int i = leftArgs.size(); i < maxVars; i++)
            leftArgs.add(TRSTerm.createVariable(fng.getFreshName("x", false)));
        TRSFunctionApplication l_new = TRSFunctionApplication.createFunctionApplication(FunctionSymbol.create(l.getName(), maxVars), leftArgs);

        TRSTerm r = rule.getRight();
        final ArrayList<TRSTerm> rightArgs = new ArrayList<TRSTerm>();

        if(r instanceof TRSFunctionApplication) {
            rightArgs.addAll(((TRSFunctionApplication) r).getArguments());
        }

        for(int i = rightArgs.size(); i < maxVars; i++)
            rightArgs.add(TRSTerm.createVariable(fng.getFreshName("x", false)));

        TRSFunctionApplication r_new = TRSFunctionApplication.createFunctionApplication(FunctionSymbol.create(r.getName(), maxVars), rightArgs);

        return new IGeneralizedRule(l_new, r_new, this.condTerm);
    }

    /** @return the integer condition term */
    public TRSTerm getCondTerm() {
        return this.condTerm == null ? ToolBox.buildTrue() : this.condTerm;
    }

    /**
     * @return The variables in the condition.
     */
    public Set<TRSVariable> getCondVariables() {
        if (this.condTerm == null) {
            return Collections.emptySet();
        }
        return this.condTerm.getVariables();
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        final Set<FunctionSymbol> fs = this.rule.getFunctionSymbols();
        ;
        if (this.condTerm != null) {
            fs.addAll(this.condTerm.getFunctionSymbols());
        }
        return fs;
    }

    /** @return the lhs of the rewrite rule */
    @Override
    public TRSFunctionApplication getLeft() {
        return this.rule.getLeft();
    }

    public List<TRSTerm> getLeftOutputVariables() {
        return this.leftOutputVariables;
    }

    /** @return the rhs of the rewrite rule */
    @Override
    public TRSTerm getRight() {
        return this.rule.getRight();
    }

    /** @return the root symbol of the rewrite rule */
    @Override
    public FunctionSymbol getRootSymbol() {
        return this.getLeft().getRootSymbol();
    }

    /** @return the rewrite rule */
    public GeneralizedRule getRule() {
        return this.rule;
    }

    /** @return the terms of the rewrite rule */
    @Override
    public Set<? extends TRSTerm> getTerms() {
        return this.rule.getTerms();
    }

    /**
     * @return The variables in this rule.
     *
     * The variables in the condition are implicitly all-quantified, and
     * therefore not relevant
     */
    @Override
    public Set<TRSVariable> getVariables() {
        return this.rule.getVariables();
    }

    /**
     * renames the variables with given prefix and
     * numbers starting from STANDARD_NUMBER.
     * E.g., for rule = f(x,y,x1,y) -> f(y,x,x,a)
     *           prefix = x
     *           STANDARD_NUMBER = 0
     *    we obtain  f(x0,x1,x2,x1) -> f(x1,x0,x0,a).
     *
     * The standard representation of a rule is
     * rule.getWithRenumberedVariables(STANDARD_PREFIX);
     * @param prefix
     * @return
     */
    public IGeneralizedRule getWithRenumberedVariables(final String prefix) {
        final Map<TRSVariable, TRSVariable> map = new LinkedHashMap<TRSVariable, TRSVariable>();
        final ImmutablePair<? extends TRSFunctionApplication, Integer> numberedLAndInt =
                this.getLeft().renumberVariables(map, prefix, TRSTerm.STANDARD_NUMBER);
        final ImmutablePair<? extends TRSTerm, Integer> numberedRAndInt =
                this.getRight().renumberVariables(map, prefix, numberedLAndInt.y);
        final ImmutablePair<? extends TRSTerm, Integer> numberedCAndInt =
                this.getCondTerm() == null ? null : this.getCondTerm().renumberVariables(map, prefix, numberedRAndInt.y);

        return new IGeneralizedRule(numberedLAndInt.x, numberedRAndInt.x, numberedCAndInt == null
                ? null
                : numberedCAndInt.x);
    }

    public Pair<IGeneralizedRule, Map<TRSVariable, TRSVariable>> getRenumberedRuleAndVariables(String prefix) {
        final Map<TRSVariable, TRSVariable> map = new LinkedHashMap<TRSVariable, TRSVariable>();
        final ImmutablePair<? extends TRSFunctionApplication, Integer> numberedLAndInt =
                this.getLeft().renumberVariables(map, prefix, TRSTerm.STANDARD_NUMBER);
        final ImmutablePair<? extends TRSTerm, Integer> numberedRAndInt =
                this.getRight().renumberVariables(map, prefix, numberedLAndInt.y);
        final ImmutablePair<? extends TRSTerm, Integer> numberedCAndInt =
                this.getCondTerm() == null ? null : this.getCondTerm().renumberVariables(map, prefix, numberedRAndInt.y);
        IGeneralizedRule renumberedRule = new IGeneralizedRule(numberedLAndInt.x, numberedRAndInt.x, numberedCAndInt == null
                ? null
                : numberedCAndInt.x);
        return new Pair<>(renumberedRule, map);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.toFullGeneralizedRule().hashCode();
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    private final static String VAR_PREFIX = "_";
    public final static String VAR = "x";

    public String getTransitionId(XMLMetaData xmlMetaData) {

        return xmlMetaData.getLtsId(this);
    }

    @Override
    public Element toCPF(Document doc, XMLMetaData xmlMetaData) {
        String transitionId = this.getTransitionId(xmlMetaData);
        Element id = CPFTag.LTS_TRANSITION_ID.create(doc, transitionId);
        Element source = CPFTag.LTS_SOURCE.create(doc, CPFTag.LTS_LOCATION_ID.create(doc, this.getRootSymbol().getName()));
        TRSTerm right = this.getRight();
        Element target;
        if (right instanceof TRSFunctionApplication) {
            TRSFunctionApplication r = (TRSFunctionApplication) right;
            target = CPFTag.LTS_TARGET.create(doc, CPFTag.LTS_LOCATION_ID.create(doc, r.getName()));
            Element conjunction = CPFTag.LTS_CONJUNCTION.create(doc);
            int i = 0;
            for (TRSTerm li : this.getLeft().getArguments()) {
                i++;
                Element xi = CPFTag.LTS_VARIABLE_ID.create(doc, VAR + i);
                Element si = toCPF(doc, VAR_PREFIX, li);
                Element eq = CPFTag.LTS_EQ.create(doc, xi, si);
                conjunction.appendChild(eq);
            }
            i = 0;
            for (TRSTerm ri : r.getArguments()) {
                i++;
                Element xi = CPFTag.LTS_POST_VARIABLE.create(doc,CPFTag.LTS_VARIABLE_ID.create(doc, VAR + i));
                Element si = toCPF(doc, VAR_PREFIX, ri);
                Element eq = CPFTag.LTS_EQ.create(doc, xi, si);
                conjunction.appendChild(eq);
            }
            TRSTerm cond = this.getCondTerm();
            if (cond != null) {
                conjunction.appendChild(toCPF(doc, VAR_PREFIX, cond));
            }
            Element formula = CPFTag.LTS_FORMULA.create(doc, conjunction);
            return CPFTag.LTS_TRANSITION.create(doc, id, source, target, formula);
        } else {
            throw new RuntimeException("error in CPF export of rule " + this.toString());
        }
    }

    public static boolean isNumeric(String str)
    {
      return str.matches("-?\\d+");  //match a number with optional '-'
    }

    private static Element toCPF(Document doc, String prefix, CPFTag tag, Iterable<? extends TRSTerm> ts) {
        Element e = tag.create(doc);
        for (TRSTerm t : ts) {
            e.appendChild(toCPF(doc, prefix, t));
        }
        return e;
    }

    public static Element toCPF(Document doc, String prefix, TRSTerm t) {

        if (t instanceof Variable) {
            return CPFTag.LTS_VARIABLE_ID.create(doc, prefix + ((Variable) t).getName());
        }
        TRSFunctionApplication ft = (TRSFunctionApplication) t;
        FunctionSymbol f = ft.getRootSymbol();
        String ff = f.getName();
        List<TRSTerm> args = ft.getArguments();
        int n = f.getArity();
        if (n == 0 && isNumeric(ff)) {
            return CPFTag.LTS_CONSTANT.create(doc, new BigInteger(ff));
        }
        if ("+".equals(ff)) {
            return toCPF(doc, prefix, CPFTag.LTS_SUM, args);
        }
        if ("*".equals(ff)) {
            return toCPF(doc, prefix, CPFTag.LTS_PRODUCT, args);
        }
        if ("&&".equals(ff)) {
            return toCPF(doc, prefix, CPFTag.LTS_CONJUNCTION, args);
        }
        if ("TRUE".equals(ff) && n == 0) {
            return CPFTag.LTS_CONJUNCTION.create(doc);
        }
        if ("<=".equals(ff) && n == 2) {
            return toCPF(doc, prefix, CPFTag.LTS_LEQ, args);
        }
        if ("=".equals(ff) && n == 2) {
            return toCPF(doc, prefix, CPFTag.LTS_EQ, args);
        }
        if ("<".equals(ff) && n == 2) {
            return toCPF(doc, prefix, CPFTag.LTS_LESS, args);
        }
        if (">=".equals(ff) && n == 2) {
            return CPFTag.LTS_LEQ.create(doc, toCPF(doc, prefix, args.get(1)), toCPF(doc, prefix, args.get(0)));
        }
        if (">".equals(ff) && n == 2) {
            return CPFTag.LTS_LESS.create(doc, toCPF(doc, prefix, args.get(1)), toCPF(doc, prefix, args.get(0)));
        }
        if ("-".equals(ff) && n == 2) {
            Element x = toCPF(doc, prefix, args.get(0));
            Element y = CPFTag.LTS_PRODUCT.create(doc, CPFTag.LTS_CONSTANT.create(doc, -1), toCPF(doc, prefix, args.get(1)));
            return CPFTag.LTS_SUM.create(doc, x, y);
        }
        throw new RuntimeException("unknown predefined function: " + f);
    }

    /**
     * Asserts that the given rule set contains a rule for each function symbol in the given set.
     *
     * No assertions are done if <code>Globals.useAssertions</code> is <code>false</code>
     *
     * @param rules The rules in which to look for the function symbol
     * @param functionSymbols The function symbol to look for
     * @throws AssertionError If there is a function symbol in <code>functionSymbols</code> for
     * which there is no rule in <code>rules</code> that has it on the left-hand-side
     */
    public static void assertSetContainsRuleForFunctionSymbols(Set<IGeneralizedRule> rules, Set<FunctionSymbol> functionSymbols) {
        if (Globals.useAssertions) {
            for (FunctionSymbol fs : functionSymbols) {
                boolean fsFound = false;
                for (IGeneralizedRule rule : rules) {
                    if (rule.getLeft().getFunctionSymbol().equals(fs)) {
                        fsFound = true;
                        break;
                    }
                }
                assert fsFound;
            }
        }
    }

    /**
     * Asserts that the given rule set contains a rule that maps from the given function symbol.
     *
     * No assertions are done if <code>Globals.useAssertions</code> is <code>false</code>
     *
     * @param rules The rules in which to look for the function symbol
     * @param fs The function symbol to look for. If <code>null</code> no checks are performed
     * @throws AssertionError If <code>rules</code> do not contain a rule that has the given
     * function symbol on the left-hand-side
     */
    public static void assertSetContainsRuleForFunctionSymbol(Set<IGeneralizedRule> rules, FunctionSymbol fs) {
        if (Globals.useAssertions) {
            if (fs != null) {
                assertSetContainsRuleForFunctionSymbols(rules, Collections.singleton(fs));
            }
        }
    }

    /**
     * Get resulting TRS rule based on the given renaming map
     *
     * @param renamingMap
     * @return resulting TRS rule
     */
    public IGeneralizedRule getWithRenamedVariables(Map<TRSVariable, TRSVariable> renamingMap) {
        TRSFunctionApplication lhs = this.getLeft().renameVariables(renamingMap);
        TRSTerm rhs = this.getRight().renameVariables(renamingMap);
        TRSTerm conditionTerm = this.getCondTerm() == null ? null : this.getCondTerm().renameVariables(renamingMap);
        return new IGeneralizedRule(lhs, rhs, conditionTerm);
    }

    public Set<TRSVariable> getAllVariables() {
        return Collection_Util.union(this.getVariables(), this.getCondVariables());
    }

}
