package aprove.verification.oldframework.IntTRS;

import java.io.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.IntegerConstraintCleaner.*;
import aprove.verification.oldframework.IRSwT.Digraph.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Debug.*;
import aprove.verification.oldframework.IntTRS.TerminationGraph.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Integer Rewrite System with Terms (IRSwT).
 * Consists of rules of the form
 * f(t_1, ..., t_n) -> g(s_1, ..., s_m) | \phi
 * where the arguments t_1, ..., t_n, s_1, ..., s_m are terms that only use
 * non-defined symbols (i.e., symbols h for which no rule h(...) -> ...)
 * exists. The right arguments s_1, ...,s_m  might additionally use basic arithmetical
 * operations (+,-,* and constants).
 *
 * To apply such a rule the instantiation of the variables has to satisfy the condition \phi, which
 * is a conjunction of atomic formulae over the signature {+, -, *, > (,=)} \cup \mathbb{Z}.
 * Variables not occurring in \phi or in arithmetical operations may be instantiated by terms consisting
 * of constructor symbols.
 *
 * Example:
 * f(x,y) -> g(x,y) | TRUE
 * g(s(x),y) -> g(x,y) | TRUE
 * g(0,y) -> f(z,y-1) | y > 0
 *
 * Here we have the following decreasing ->-chain:
 * f(s(0),1) -> g(s(0),1) -> g(0,1) -> f(s(s(17)),0) -> ...
 *
 * Please note that every variable occurring in an arithmetical operation or in \phi has to be instantiated by an
 * integer.
 *
 * @author Marc Brockschmidt, Matthias Hoelzel, Carsten Fuhs, cryingshadow
 */
public class IRSwTProblem extends DefaultBasicObligation implements IRSLike {

    /**
     * @param rules the rules to export
     * @param aborter tells us when to abort
     * @param writer a writer to which we export
     * @throws IOException the exception that can be thrown by the writer.
     * @throws AbortionException can be aborted
     */
    public static void exportRules(final Set<IGeneralizedRule> rules, final Abortion aborter, final Writer writer)
    throws IOException, AbortionException {
        final Export_Util eu = new PLAIN_Util();
        final StringBuilder intTRSSB = new StringBuilder();
        for (final IGeneralizedRule rule : rules) {
            IRSwTProblem.exportRule(rule, eu, aborter, intTRSSB);
            intTRSSB.append("\n");
        }
        writer.write(intTRSSB.toString());
    }

    private static boolean areVariableNamesIllegal(final Set<TRSVariable> ruleVars) {
        for (final TRSVariable v : ruleVars) {
            final String name = v.getName();
            if (name.startsWith("div") || name.startsWith("plus") || name.startsWith("minus")
                || name.startsWith("mult")) {
                return true;
            }
        }
        return false;
    }

    /**
     * @param args A list of sets of terms.
     * @return A set of lists of terms with all combinations of the terms in the specified sets (i.e., if the list of
     *         sets is [{1,2},{3},{4,5}], then the resulting set of lists is {[1,3,4],[1,3,5],[2,3,4],[2,3,5]}).
     */
    private static Set<ArrayList<TRSTerm>> combine(List<Set<TRSTerm>> args) {
        if (args.isEmpty()) {
            return Collections.singleton(new ArrayList<TRSTerm>());
        }
        List<Set<TRSTerm>> withoutLast = new ArrayList<Set<TRSTerm>>(args);
        Set<TRSTerm> set = withoutLast.remove(withoutLast.size() - 1);
        Set<ArrayList<TRSTerm>> resWithoutLast = IRSwTProblem.combine(withoutLast);
        Set<ArrayList<TRSTerm>> res = new LinkedHashSet<ArrayList<TRSTerm>>();
        for (TRSTerm t : set) {
            for (ArrayList<TRSTerm> list : resWithoutLast) {
                ArrayList<TRSTerm> toAdd = new ArrayList<TRSTerm>(list);
                toAdd.add(t);
                res.add(toAdd);
            }
        }
        return res;
    }

    /**
     * Constructs a substitution for renaming variables in a canonical way. The specified substitution is extended
     * accordingly.
     * @param t Some non-variable term.
     * @param subst A substitution.
     * @param index An index for fresh variable names.
     * @return The index for the next fresh variable.
     */
    private static int computeSubstitution(TRSFunctionApplication t, Map<TRSTerm, TRSTerm> subst, int index) {
        int i = index;
        for (TRSTerm arg : t.getArguments()) {
            if (arg.isVariable()) {
                if (!subst.containsKey(arg)) {
                    subst.put(arg, TRSTerm.createVariable("x_" + i++));
                }
            } else {
                i = IRSwTProblem.computeSubstitution((TRSFunctionApplication)arg, subst, i);
            }
        }
        return i;
    }

    /**
     * Creates and returns a brand new fresh name generator.
     * @return FreshNameGenerator
     */
    private static FreshNameGenerator createFreshNameGenerator(final Set<IGeneralizedRule> rules) {
        final FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        for (final IGeneralizedRule rule : rules) {
            IRSwTProblem.lockNames(rule, fng);
        }
        return fng;
    }

    /**
     * @param rule some rule
     * @param eu an export util
     * @param aborter tells us when to abort
     * @param sb a StringBuilder to which the rule is written
     * @throws AbortionException can be aborted
     */
    private static void exportRule(
        final IGeneralizedRule rule,
        final Export_Util eu,
        final Abortion aborter,
        final StringBuilder sb
    ) throws AbortionException {
        final TRSTerm condTerm = rule.getCondTerm();
        final Set<String> exportedConds = new LinkedHashSet<String>();
        if (condTerm != null && !condTerm.equals(ToolBox.buildTrue())) {
            assert (!condTerm.isVariable()) : "Cond is variable -> should have been removed.";

            final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
            final List<IntegerConstraintRelation> splittedRelations = IntegerConstraintCleaner.takeApart(condTerm, fne);

            for (final IntegerConstraintRelation rel : splittedRelations) {
                exportedConds.add(IDPExport.exportTerm(
                    RuleSimplification.simplifyCondition(rel.toDPTerm(), fne, aborter).x,
                    eu,
                    IDPPredefinedMap.DEFAULT_MAP));
            }
        }

        String lhs = IDPExport.exportTerm(rule.getLeft(), eu, IDPPredefinedMap.DEFAULT_MAP);
        if (!lhs.endsWith(")")) {
            lhs = lhs + "()";
        }
        sb.append(lhs);
        sb.append(" -> ");

        final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        fne.lockHasNames(rule.getRight().getVariables());
        String rhs =
            IDPExport.exportTerm(
                RuleSimplification.simplifyTerm(rule.getRight(), fne, aborter),
                eu,
                IDPPredefinedMap.DEFAULT_MAP);
        if (!rhs.endsWith(")")) {
            rhs = rhs + "()";
        }
        sb.append(rhs);

        if (exportedConds.size() > 0) {
            sb.append(" [ ");
            boolean isFirst = true;
            for (final String cond : exportedConds) {
                if (!isFirst) {
                    sb.append(" /\\ ");
                }
                sb.append(cond);
                isFirst = false;
            }
            sb.append(" ]");
        }
    }

    /**
     * Passes the names of a given rule to a fresh name generator.
     * @param rule current rule
     * @param fng fresh name generator to be initialized
     */
    private static void lockNames(final IGeneralizedRule rule, final FreshNameGenerator fng) {
        IRSwTProblem.lockNames(rule.getLeft(), fng);
        IRSwTProblem.lockNames(rule.getRight(), fng);
        final TRSTerm condTerm = rule.getCondTerm();
        if (condTerm != null) {
            IRSwTProblem.lockNames(condTerm, fng);
        }
    }

    /**
     * Passes the names of a given term.
     * @param t current term
     * @param fng fresh name generator to be initialized
     */
    private static void lockNames(final TRSTerm t, final FreshNameGenerator fng) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication f = (TRSFunctionApplication) t;
            fng.lockName(f.getRootSymbol().getName());
            for (final TRSTerm arg : f.getArguments()) {
                IRSwTProblem.lockNames(arg, fng);
            }
        } else if (t instanceof TRSVariable) {
            final TRSVariable v = (TRSVariable) t;
            fng.lockName(v.getName());
        } else {
            assert false : "Strange term!";
        }
    }

    /**
     * Rename variables in rewriting rules to make them disjoint
     *
     * @param inputRules
     * @return
     */
    private static
    Pair<ImmutableSet<IGeneralizedRule>, LinkedHashMap<IGeneralizedRule, IGeneralizedRule>>
    makeVariableDisjoint(final Set<IGeneralizedRule> inputRules)
    {
        final LinkedHashSet<IGeneralizedRule> resultRules = new LinkedHashSet<>();
        final LinkedHashMap<IGeneralizedRule, IGeneralizedRule> history = new LinkedHashMap<>();

        // Initialized Name Generator:
        final FreshNameGenerator fng = IRSwTProblem.createFreshNameGenerator(inputRules);

        final LinkedHashSet<TRSVariable> seenVariables = new LinkedHashSet<>();

        for (final IGeneralizedRule rule : inputRules) {
            final Set<TRSVariable> ruleVars = rule.getVariables();
            ruleVars.addAll(rule.getCondVariables());

            // Test whether or not the current and some other rule share some variables:
            boolean renameVariables = false;
            for (final TRSVariable v : ruleVars) {
                if (seenVariables.contains(v)) {
                    renameVariables = true;
                    break;
                }
            }

            // Does the rule contains strange variable names?
            if (IRSwTProblem.areVariableNamesIllegal(ruleVars)) {
                renameVariables = true;
            }

            // Rename if necessary:
            if (renameVariables) {
                // Constructor renaming substitution:
                final LinkedHashMap<TRSVariable, TRSTerm> renaming = new LinkedHashMap<>();
                for (final TRSVariable v : ruleVars) {
                    renaming.put(v, TRSTerm.createVariable(fng.getFreshName("x", false)));
                }
                final TRSSubstitution renamingSubstitution = TRSSubstitution.create(ImmutableCreator.create(renaming));

                final TRSFunctionApplication newLeftSide = rule.getLeft().applySubstitution(renamingSubstitution);
                final TRSTerm newRightSide = rule.getRight().applySubstitution(renamingSubstitution);
                final TRSTerm newCondition =
                    rule.getCondTerm() == null ? ToolBox.buildTrue() : rule.getCondTerm().applySubstitution(
                        renamingSubstitution);
                    final IGeneralizedRule renamedRule = IGeneralizedRule.create(newLeftSide, newRightSide, newCondition);

                    history.put(rule, renamedRule);

                    // Remember what we did here:
                    seenVariables.addAll(renamedRule.getVariables());
                    seenVariables.addAll(renamedRule.getCondVariables());

                    resultRules.add(renamedRule);
            } else {
                // Remember the names:
                seenVariables.addAll(ruleVars);
                for (final TRSVariable v : ruleVars) {
                    fng.lockName(v.getName());
                }

                resultRules.add(rule);
            }
        }

        return new Pair<ImmutableSet<IGeneralizedRule>, LinkedHashMap<IGeneralizedRule, IGeneralizedRule>>(
            ImmutableCreator.create(resultRules),
            history);
    }

    /**
     * @param t Some non-variable term.
     * @return An equivalent term where all variables are renamed in a canonical way.
     */
    private static TRSFunctionApplication normalize(TRSFunctionApplication t) {
        Map<TRSTerm, TRSTerm> subst = new LinkedHashMap<TRSTerm, TRSTerm>();
        IRSwTProblem.computeSubstitution(t, subst, 1);
        return (TRSFunctionApplication)t.replaceAll(subst);
    }

    /**
     * @param rule Some rule.
     * @return An equivalent rule where all variables are renamed in a canonical way.
     */
    private static IGeneralizedRule normalize(IGeneralizedRule rule) {
        TRSFunctionApplication left = rule.getLeft();
        TRSTerm right = rule.getRight();
        TRSTerm cond = rule.getCondTerm();
        Map<TRSTerm, TRSTerm> subst = new LinkedHashMap<TRSTerm, TRSTerm>();
        int i = IRSwTProblem.computeSubstitution(left, subst, 1);
        if (right.isVariable()) {
            if (!subst.containsKey(right)) {
                subst.put(right, TRSTerm.createVariable("x_" + i++));
            }
        } else {
            i = IRSwTProblem.computeSubstitution((TRSFunctionApplication)right, subst, i);
        }
        if (cond.isVariable()) {
            if (!subst.containsKey(cond)) {
                subst.put(cond, TRSTerm.createVariable("x_" + i++));
            }
        } else {
            IRSwTProblem.computeSubstitution((TRSFunctionApplication)cond, subst, i);
        }
        return
            IGeneralizedRule.create(
                (TRSFunctionApplication)left.replaceAll(subst),
                right.replaceAll(subst),
                cond.replaceAll(subst)
            );
    }

    /**
     * @param rules A set of rules.
     * @return An equivalent set of rules where all variables are renamed in a canonical way.
     */
    private static Set<IGeneralizedRule> normalize(Set<IGeneralizedRule> rules) {
        Set<IGeneralizedRule> res = new LinkedHashSet<IGeneralizedRule>();
        for (IGeneralizedRule rule : rules) {
            res.add(IRSwTProblem.normalize(rule));
        }
        return res;
    }

    /** The actual rules. */
    private final ImmutableSet<IGeneralizedRule> rules;

    /** The start term. May be null, which means we don't have no start term. */
    private final TRSFunctionApplication startTerm;

    /** A partially evaluated termination digraph. */
    private final PartiallyComputedDigraph<IGeneralizedRule> terminationDigraph;

    /**
     * @param r the rules
     */
    public IRSwTProblem(final ImmutableSet<IGeneralizedRule> r) {
        this(r, null, null);
    }

    /**
     * @param r the rules
     * @param start the start term
     */
    public IRSwTProblem(final ImmutableSet<IGeneralizedRule> r, final TRSFunctionApplication start) {
        this(r, null, start);
    }

    /**
     * @param r the rules
     * @param digraph the partially computed termination digraph (will be frozen).
     */
    public IRSwTProblem(final ImmutableSet<IGeneralizedRule> r, final PartiallyComputedDigraph<IGeneralizedRule> digraph)
    {
        this(r, digraph, null);
    }

    /**
     * @param r the rules
     * @param start the start term
     */
    public IRSwTProblem(
        final ImmutableSet<IGeneralizedRule> r,
        final PartiallyComputedDigraph<IGeneralizedRule> digraph,
        final TRSFunctionApplication start)
    {
        this(r, digraph, start, "IRSwT", "IRSwT problem");
    }

    /**
     * @param r the rules
     * @param start the start term
     */
    protected IRSwTProblem(
        final ImmutableSet<IGeneralizedRule> r,
        final PartiallyComputedDigraph<IGeneralizedRule> digraph,
        final TRSFunctionApplication start,
        final String shortName,
        final String longName)
    {
        super(shortName, longName);
        final Pair<ImmutableSet<IGeneralizedRule>, LinkedHashMap<IGeneralizedRule, IGeneralizedRule>> disjointPair =
            IRSwTProblem.makeVariableDisjoint(r);

        this.rules = disjointPair.x;
        //this.rules = r;
        if (digraph != null) {
            this.terminationDigraph =
                disjointPair.y.isEmpty() ? digraph : digraph.translateNodes(disjointPair.x, disjointPair.y);
            this.terminationDigraph.freeze();
        } else {
            this.terminationDigraph = null;
        }

        this.startTerm = start;

        Log.report("IntTRS", this.toString());
    }

    
    /**
     * Creates and returns a brand new fresh name generator.
     * @return FreshNameGenerator
     */
    public FreshNameGenerator createFreshNameGenerator() {
        final FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        for (final IGeneralizedRule rule : this.rules) {
            IRSwTProblem.lockNames(rule, fng);
        }
        return fng;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof IRSwTProblem)) {
            return false;
        }
        final IRSwTProblem other = (IRSwTProblem) obj;
        if (this.rules == null) {
            if (other.rules != null) {
                return false;
            }
        } else if (!this.rules.equals(other.rules)) {
            return false;
        }
        return true;
    }

    public boolean equalsModuloVariableRenaming(IRSwTProblem p) {
        TRSFunctionApplication s = p.getStartTerm();
        if (s == null) {
            if (this.getStartTerm() != null) {
                return false;
            }
        } else {
            TRSFunctionApplication t = this.getStartTerm();
            if (t == null) {
                return false;
            }
            if (!IRSwTProblem.normalize(s).equals(IRSwTProblem.normalize(t))) {
                return false;
            }
        }
        Set<IGeneralizedRule> thisRules = IRSwTProblem.normalize(this.getRules());
        Set<IGeneralizedRule> otherRules = IRSwTProblem.normalize(p.getRules());
        return thisRules.containsAll(otherRules) && otherRules.containsAll(thisRules);
    }

    /** {@inheritDoc} */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder res = new StringBuilder();

        if (this.terminationDigraph == null || !this.terminationDigraph.getVertices().equals(this.rules)) {
            res.append("Rules:").append(o.linebreak());
            for (final IGeneralizedRule r : this.rules) {
                res.append(r.export(o)).append(o.linebreak());
            }
        }
        if (this.terminationDigraph != null) {
            res.append(o.linebreak()).append("Termination digraph:").append(o.linebreak());
            res.append(this.terminationDigraph.export(o));
            res.append(o.linebreak());
        }

        if (this.startTerm != null) {
            res.append("Start term: ").append(this.startTerm.export(o)).append(o.linebreak());
        }

        return res.toString();
    }

    /** {@inheritDoc} */
    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    /**
     * @return the rules
     */
    public ImmutableSet<IGeneralizedRule> getRules() {
        return this.rules;
    }

    /**
     * @return the start term
     */
    public TRSFunctionApplication getStartTerm() {
        return this.startTerm;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "irswt";
    }

    /**
     * Returns the partial computed termination digraph.
     * @return a partially evaluated termination digraph
     */
    public PartiallyComputedDigraph<IGeneralizedRule> getTerminationDigraph() {
        return this.terminationDigraph;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.rules == null) ? 0 : this.rules.hashCode());
        return result;
    }

    /** Returns true, if this uses some cast symbols. */
    public boolean isBounded() {
        return false;
    }

    /**
     * Returns true iff this problem does not use terms.
     * @return boolean
     */
    public boolean isIRS() {
        boolean result = this.areIRSRules(this.getRules());
        if (this.getStartTerm() != null) {
            result = result && this.checkIRSSides(this.getStartTerm());
        }
        return result;
    }

    @Override
    public String toString() {
        final StringBuilder result = new StringBuilder("intTRSProblem:\n");

        if (this.startTerm != null) {
            result.append("START: ");
            result.append(this.startTerm);
            result.append("\n");
        }

        int counter = this.rules.size();
        for (final IGeneralizedRule rule : this.rules) {
            result.append(rule.toString());
            counter--;
            if (counter != 0) {
                result.append("\n");
            }
        }
        return result.toString();
    }

    private boolean areIRSRules(final ImmutableSet<IGeneralizedRule> rules) {
        if (rules == null) {
            return false;
        }
        for (final IGeneralizedRule rule : rules) {
            final TRSFunctionApplication funcLeft = rule.getLeft();
            final TRSTerm right = rule.getRight();
            assert right instanceof TRSFunctionApplication : "Expected function application!";
            final TRSFunctionApplication funcRight = (TRSFunctionApplication) right;

            if (!(this.checkIRSSides(funcLeft) && this.checkIRSSides(funcRight))) {
                return false;
            }
        }
        return true;
    }

    private boolean checkIRSSides(final TRSFunctionApplication func) {
        for (final TRSTerm arg : func.getArguments()) {
            if (!this.isIRSArgument(arg)) {
                return false;
            }
        }
        return true;
    }

    private boolean isIRSArgument(final TRSTerm arg) {
        if (arg instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) arg;
            final FunctionSymbol sym = func.getRootSymbol();
            if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                return false;
            }
            for (final TRSTerm nextArg : func.getArguments()) {
                if (!this.isIRSArgument(nextArg)) {
                    return false;
                }
            }
        }
        return true;
    }
    
    @Override
    public Element getCPFInput(final Document doc, XMLMetaData xmlMetaData, final TruthValue tv) {
        if (xmlMetaData == null) {
            xmlMetaData = createInitialMetaData(this);
        }
        TRSFunctionApplication optStart = this.getStartTerm();
        Set<FunctionSymbol> initialSyms = new HashSet<>();
        if (optStart == null) {
            for (IGeneralizedRule rule : this.getRules()) {
                initialSyms.add(rule.getRootSymbol());
            } 
        } else {
            initialSyms.add(optStart.getRootSymbol());
        }
        Element initial = CPFTag.LTS_INITIAL.create(doc);
        for (FunctionSymbol init : initialSyms) {
            initial.appendChild(CPFTag.LTS_LOCATION_ID.create(doc, init.getName()));
        }
        Element lts = CPFTag.LTS_INPUT.create(doc, initial);
        for (IGeneralizedRule rule : this.getRules()) {
            lts.appendChild(rule.toCPF(doc, xmlMetaData));
        }
        
        return lts;
    }
    
    public static XMLMetaData createInitialMetaData(IRSLike irs) {
        final Map<IGeneralizedRule, String> ruleToId = new LinkedHashMap<>();
        int i = 1;
        Set<FunctionSymbol> fs = new HashSet<>();
        for (final IGeneralizedRule rule : irs.getRules()) {
            ruleToId.put(rule, i + "");
            fs.add(rule.getRootSymbol());
            i++;
        }
        Map<FunctionSymbol, List<String>> fsMap = new HashMap<>();
        for (FunctionSymbol f : fs) {
            int n = f.getArity();
            List<String> vars = new ArrayList<>(n);
            for (i = 1; i <= n; i++) {
        		String x = IGeneralizedRule.VAR + i;
        		vars.add(x);        		
            }
            fsMap.put(f, vars);
        }
        return new XMLMetaData(ruleToId, fsMap); 
    }
    
    public Element getCPFAssumption(Document doc, XMLMetaData xmlMetaData, CPFModus modus, TruthValue result) {
        return CPFTag.UNKNOWN_INPUT_PROOF.create(doc,
                CPFTag.UNKNOWN_ASSUMPTION.create(
                        doc,
               this.getCPFInput(doc, createInitialMetaData(this), result)));        
    }


    @Override
    public IRSLike create(Set<IGeneralizedRule> rules, TRSFunctionApplication startTerm) {
        return new IRSwTProblem(ImmutableCreator.create(rules), startTerm);
    }

}
