package aprove.verification.complexity.CpxIntTrsProblem;

import java.io.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.input.Programs.cint.Translator;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Algorithms.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Complexity IntTRS Problems, a simple formalism for complexity analysis.
 * <p>
 * Hopefully.
 * </p>
 * <p>
 * <b>Important:</b> When dealing with {@link CpxIntTrsProblem}s a simplifying
 * assumption is that only {@link IDPPredefinedMap#DEFAULT_MAP} is used to give
 * predefined symbols semantics.
 * </p>
 */
public class CpxIntTrsProblem extends DefaultBasicObligation implements ExternUsable {

    /**
     * All (conditional) rules of the system.
     */
    private final ImmutableLinkedHashMap<CpxIntTupleRule, ComplexityValue> k;

    /**
     * The set of allowed start symbols.
     */
    private final ImmutableLinkedHashSet<FunctionSymbol> g;

    /**
     * Cached things
     */
    private CpxIntGraph depGraph = null;

    private ImmutableLinkedHashMap<CallArgument, LocalComplexityValue> sizeBounds = null;

    private CpxIntTrsProblem(
        final ImmutableLinkedHashMap<CpxIntTupleRule, ComplexityValue> k,
        final ImmutableLinkedHashSet<FunctionSymbol> g)
    {
        super("CpxIntTrs", "CpxIntTrs");

        this.k = k;
        this.g = g;

    }

    private CpxIntTrsProblem(
        ImmutableLinkedHashMap<CpxIntTupleRule, ComplexityValue> k,
        ImmutableLinkedHashSet<FunctionSymbol> g,
        CpxIntGraph depGraph)
    {
        super("CpxIntTrs", "CpxIntTrs");
        this.k = k;
        this.g = g;
        this.depGraph = depGraph;

        if (Globals.useAssertions) {
            assert k.keySet().equals(this.getDepGraph(AbortionFactory.create()).getRules());
        }
    }

    /**
     * @param rules All (conditional) rules of the system.
     * @return The corresponding {@link CpxIntTrsProblem}.
     */
    public static CpxIntTrsProblem create(
        final ImmutableLinkedHashSet<CpxIntTupleRule> rules,
        ImmutableLinkedHashSet<FunctionSymbol> g)
    {
        LinkedHashMap<CpxIntTupleRule, ComplexityValue> k = new LinkedHashMap<>();
        for (CpxIntTupleRule rule : rules) {
            k.put(rule, ComplexityValue.infinite());
        }
        return new CpxIntTrsProblem(ImmutableCreator.create(k), g);
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new ComplexityProofPurposeDescriptor(this, "runtime complexity");
    }

    @Override
    public String export(final Export_Util eu) {
        StringBuilder s = new StringBuilder();
        Abortion aborter = AbortionFactory.create();
        s.append(eu.export("Complexity Int TRS consisting of the following rules:") + eu.cond_linebreak());
        for (Entry<CpxIntTupleRule, ComplexityValue> entry : this.k.entrySet()) {
            CpxIntTupleRule rule = entry.getKey();
            ComplexityValue complexity = entry.getValue();
            if (!complexity.isInfinite()) {
                s.append(complexity);
                s.append(": ");
            }
            s.append(rule.export(eu));
            s.append(eu.cond_linebreak());
        }
        s.append(eu.cond_linebreak());
        s.append(eu.export("The start-symbols are:") + eu.export(this.g) + eu.cond_linebreak());

        s.append(eu.cond_linebreak());
        if (sizeBounds != null) {
            s.append(eu.export("The dependency graph:") + eu.cond_linebreak());
            s.append(this.depGraph.export(eu, this.k, sizeBounds, this.getG()));
            s.append(eu.cond_linebreak());
            CallArgumentGraph callgraph;
            try {
                callgraph = SizeBoundComputation.buildCallArgumentGraph(this.getDepGraph(aborter), aborter);
            } catch (AbortionException e) {
                throw new RuntimeException(e);
            }
            s.append(eu.export("The call argument graph:") + eu.cond_linebreak());
            s.append("<textarea>"
                + eu.escape(callgraph.toDOT(this.getG(), sizeBounds))
                + "</textarea>");
        }

        return s.toString();
    }

    /**
     * @return All (conditional) rules of the system. The returned set cannot be
     * modified.
     */
    public Set<Entry<CpxIntTupleRule, ComplexityValue>> getC() {
        return this.k.entrySet();
    }

    /**
     * @return All (conditional) rules of the system.
     */
    public ImmutableLinkedHashMap<CpxIntTupleRule, ComplexityValue> getK() {
        return this.k;
    }

    @Override
    public String getStrategyName() {
        return "cint";
    }

    @Override
    public String toExternString() throws NotExternUsableInstanceException {
        final StringBuilder s = new StringBuilder();
        final Set<TRSVariable> vars = new LinkedHashSet<>();
        for (final CpxIntTupleRule rule : this.k.keySet()) {
            vars.addAll(rule.getVariables());
        }
        final Set<String> varNames = new LinkedHashSet<>();
        for (final TRSVariable x : vars) {
            varNames.add(x.getName());
        }
        final Set<String> definedNames = new LinkedHashSet<>();
        for (final FunctionSymbol f : this.getDefinedSymbols()) {
            definedNames.add(f.getName());
        }

        final FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
        fng.lockNames(definedNames);
        fng.lockNames(varNames);

        final Set<String> collisions = new LinkedHashSet<>(varNames);
        collisions.retainAll(definedNames);

        final Map<TRSVariable, TRSVariable> varMap = new LinkedHashMap<>();
        for (final TRSVariable x : vars) {
            if (collisions.contains(x.toString())) {
                varMap.put(x, TRSTerm.createVariable(fng.getFreshName(x.toString(), false)));
            } else {
                varMap.put(x, x);
            }
        }
        final TRSSubstitution subst = TRSSubstitution.create(ImmutableCreator.create(varMap));

        // output
        s.append("(GOAL COMPLEXITY)\n");
        s.append("(STARTTERM (FUNCTIONSYMBOLS");
        Set<String> startsyms = new LinkedHashSet<>();
        for (FunctionSymbol fs : this.g) {
            if (startsyms.contains(fs.getName())) {
                throw new RuntimeException("Symbol " + fs.getName() + " occurs with different arities.");
            }
            s.append(' ');
            s.append(fs.getName());
        }
        s.append("))\n");
        s.append("(VAR");
        for (final TRSVariable var : varMap.values()) {
            s.append(" " + var.toString());
        }
        s.append(")\n");
        s.append("(RULES\n");
        for (CpxIntTupleRule rule : this.k.keySet()) {
            s.append("  ");
            try {
                s.append(rule.applySubstitution(subst).export(new PLAIN_Util()));
            } catch (NoConstraintTermException e) {
                // does not happen, since subst is only a variable renaming
                throw new RuntimeException(e);
            }
            s.append("\n");
        }
        s.append(")\n");

        if (Globals.useAssertions) {
            Translator tr = new Translator();
            Reader stream = new StringReader(s.toString());
            try {
                tr.translate(stream);
            } catch (TranslationException e) {
                assert false : "translation exception";
            }
            Object o = tr.getState();
            assert this.equals(o);
        }

        return s.toString();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.g == null) ? 0 : this.g.hashCode());
        result = prime * result + ((this.k == null) ? 0 : this.k.hashCode());
        return result;
    }


    // Only checks syntactic equality of G and K.
    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        CpxIntTrsProblem other = (CpxIntTrsProblem) obj;
        if (this.g == null) {
            if (other.g != null) {
                return false;
            }
        } else if (!this.g.equals(other.g)) {
            return false;
        }
        if (this.k == null) {
            if (other.k != null) {
                return false;
            }
        } else if (!this.k.equals(other.k)) {
            return false;
        }
        return true;
    }

    @Override
    public String externName() {
        return "cint";
    }

    public LinkedHashSet<FunctionSymbol> getDefinedSymbols() {
        LinkedHashSet<FunctionSymbol> defs = new LinkedHashSet<>();
        for (CpxIntTupleRule rule : this.k.keySet()) {
            defs.add(rule.getRootSymbol());
            for (TRSFunctionApplication t : rule.getRights()) {
                defs.add(t.getRootSymbol());
            }
        }
        return defs;
    }

    public LinkedHashSet<String> getUsedVarNames() {
        LinkedHashSet<String> vars = new LinkedHashSet<>();
        for (CpxIntTupleRule rule : this.k.keySet()) {
            for (TRSVariable v : rule.getVariables()) {
                vars.add(v.getName());
            }
        }
        return vars;
    }

    public CpxIntTrsProblem updateKValues(final Map<CpxIntTupleRule, ComplexityValue> updatedTuples) {
        if (Globals.useAssertions) {
            assert updatedTuples != null;
            this.k.keySet().containsAll(updatedTuples.keySet());
        }

        LinkedHashMap<CpxIntTupleRule, ComplexityValue> k = new LinkedHashMap<>();
        k.putAll(this.k);
        for (Entry<CpxIntTupleRule, ComplexityValue> e : updatedTuples.entrySet()) {
            ComplexityValue removed = k.put(e.getKey(), e.getValue());
            assert removed != null;
            assert removed.compareTo(e.getValue()) >= 0;
        }

        return new CpxIntTrsProblem(ImmutableCreator.create(k), this.g, this.getDepGraph(AbortionFactory.create()));
    }

    public synchronized CpxIntGraph getDepGraph(Abortion aborter) {
        if (this.depGraph == null) {
            try {
                this.depGraph = CpxIntGraph.createDefaultApproximation(this.k.keySet(), aborter);
            } catch (AbortionException e) {
                throw new RuntimeException(e);
            }
        }
        return this.depGraph;
    }

    public CpxIntTrsProblem createSubproblem(
        CpxIntGraph depGraph,
        ImmutableLinkedHashMap<CpxIntTupleRule, ComplexityValue> k)
    {
        return new CpxIntTrsProblem(k, this.g, depGraph);
    }

    public BasicObligation createSubproblemByRemovingRulesCompletely(Set<CpxIntTupleRule> removed) {
        LinkedHashMap<CpxIntTupleRule, ComplexityValue> k = new LinkedHashMap<>();
        k.putAll(this.k);
        for (CpxIntTupleRule rule : removed) {
            k.remove(rule);
        }

        CpxIntGraph graph = this.getDepGraph(AbortionFactory.create()).createByRemovingRules(removed);

        Set<String> usedVarNames = new LinkedHashSet<>();
        for (CpxIntTupleRule tuple : this.k.keySet()) {
            for (TRSVariable v : tuple.getVariables()) {
                usedVarNames.add(v.getName());
            }
        }
        LinkedHashSet<FunctionSymbol> defs = this.computeDefs(k.keySet());

        LinkedHashSet<FunctionSymbol> g = new LinkedHashSet<>();
        g.addAll(this.g);
        g.retainAll(defs);

        return new CpxIntTrsProblem(ImmutableCreator.create(k), ImmutableCreator.create(g), graph);
    }

    private LinkedHashSet<FunctionSymbol> computeDefs(Set<CpxIntTupleRule> rules) {
        LinkedHashSet<FunctionSymbol> defs = new LinkedHashSet<>();
        for (CpxIntTupleRule rule : rules) {
            defs.add(rule.getRootSymbol());
            for (TRSTerm r : rule.getRight().getArguments()) {
                if (r.isVariable()) {
                    continue;
                }
                defs.add(((TRSFunctionApplication) r).getRootSymbol());
            }
        }
        return defs;
    }

    public CpxIntTrsProblem replaceRules(Map<CpxIntTupleRule, Set<CpxIntTupleRule>> replacements) {
        Set<CpxIntTupleRule> remove = replacements.keySet();

        LinkedHashMap<CpxIntTupleRule, ComplexityValue> k = new LinkedHashMap<>();
        k.putAll(this.k);
        for (CpxIntTupleRule rule : remove) {
            k.remove(rule);
        }

        for (Entry<CpxIntTupleRule, Set<CpxIntTupleRule>> e : replacements.entrySet()) {
            CpxIntTupleRule removedRule = e.getKey();
            Set<CpxIntTupleRule> addedRules = e.getValue();
            if (this.k.containsKey(removedRule)) {
                ComplexityValue complexity = this.k.get(removedRule);
                for (CpxIntTupleRule rule : addedRules) {
                    k.put(rule, complexity);
                }
            }
        }

        CpxIntGraph graph;
        try {
            graph =
                this.getDepGraph(AbortionFactory.create()).createByReplacingRules(
                    replacements,
                    AbortionFactory.create());
        } catch (AbortionException e) {
            throw new RuntimeException(e);
        }

        Set<String> usedVarNames = new LinkedHashSet<>();
        for (CpxIntTupleRule tuple : this.k.keySet()) {
            for (TRSVariable v : tuple.getVariables()) {
                usedVarNames.add(v.getName());
            }
        }

        LinkedHashSet<FunctionSymbol> defs = this.computeDefs(k.keySet());

        LinkedHashSet<FunctionSymbol> g = new LinkedHashSet<>();
        g.addAll(this.g);
        g.retainAll(defs);

        return new CpxIntTrsProblem(ImmutableCreator.create(k), ImmutableCreator.create(g), graph);
    }

    public boolean isSolved() {
        return this.getUnknownTuples().isEmpty();
    }

    /**
     * The returned set might be modified.
     * @return
     */
    public LinkedHashSet<CpxIntTupleRule> getUnknownTuples() {
        LinkedHashSet<CpxIntTupleRule> unknown = new LinkedHashSet<>();
        for (Entry<CpxIntTupleRule, ComplexityValue> entry : this.k.entrySet()) {
            if (entry.getValue().isInfinite()) {
                unknown.add(entry.getKey());
            }
        }
        return unknown;
    }

    /**
     * @return The set of allowed start symbols.
     */
    public ImmutableLinkedHashSet<FunctionSymbol> getG() {
        return this.g;
    }

    public synchronized ImmutableLinkedHashMap<CallArgument, LocalComplexityValue> getSizeBounds(Abortion aborter) {
        if (this.sizeBounds == null) {
            this.sizeBounds = SizeBoundComputation.computeSizeBounds(this, aborter);
        }
        return this.sizeBounds;
    }

    public LinkedHashSet<CpxIntTupleRule> getStartRules() {
        LinkedHashSet<CpxIntTupleRule> rv = new LinkedHashSet<>();
        LinkedHashSet<FunctionSymbol> d = this.getG();
        for (CpxIntTupleRule rho : this.getK().keySet()) {
            if (d.contains(rho.getRootSymbol())) {
                rv.add(rho);
            }
        }
        return rv;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }
}
