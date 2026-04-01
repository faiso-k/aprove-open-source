package aprove.verification.complexity.CpxRelTrsProblem;

import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public abstract class CpxRelTrsProblem extends DefaultBasicObligation implements HasTRSTerms, HasRules<Rule>, HasDefinedSymbols, ExternUsable {

    // cached / calculated values
    protected int hashCode;
    private RewriteStrategy rewriteStrategy;
    protected ImmutableSet<Rule> R;

    protected ImmutableSet<Rule> S;
    protected ImmutableSet<FunctionSymbol> signature; // signature of R \cup S

    private ImmutableSet<Rule> allRules;

    protected ImmutableSet<FunctionSymbol> defSymbols;

    /**
     * true if we proved innermost termination of S, false if we don't know if S terminates
     */
    private boolean STerminatesInnermost = false;

    /**
     * creates a relative TRS problem (where "relative" has non-standard semantics).
     * @param R - the TRS
     * @param S - the relative TRS
     * @param innermost - whether innermost evaluation is used
     */
    protected CpxRelTrsProblem(String shortname,
            String longname,
            final ImmutableSet<Rule> R,
            final ImmutableSet<Rule> S,
            Set<FunctionSymbol> definedSymbols,
            final RewriteStrategy rewriteStrategy,
            boolean STerminatesInnermost) {
        super(shortname, longname);
        init(R, S, definedSymbols, rewriteStrategy, STerminatesInnermost);
    }

    private void init(ImmutableSet<Rule> R,
            ImmutableSet<Rule> S,
            Set<FunctionSymbol> definedSymbols,
            RewriteStrategy rewriteStrategy,
            boolean STerminatesInnermost) {
        this.R = R;
        this.S = S;
        this.allRules = ImmutableCreator.create(union(R, S));
        this.rewriteStrategy = rewriteStrategy;
        this.STerminatesInnermost = STerminatesInnermost;

        final Set<FunctionSymbol> sig = CollectionUtils.getFunctionSymbols(allRules);
        this.signature = ImmutableCreator.create(sig);

        definedSymbols = new LinkedHashSet<FunctionSymbol>(definedSymbols);
        definedSymbols.retainAll(signature);
        this.defSymbols = ImmutableCreator.create(definedSymbols);

        final int prime = 31;
        int result = 1;
        result = prime * result + ((R == null) ? 0 : R.hashCode());
        result = prime * result + ((S == null) ? 0 : S.hashCode());
        result = prime * result + ((defSymbols == null) ? 0 : defSymbols.hashCode());
        result = prime * result + hashCode;
        result = prime * result + rewriteStrategy.hashCode();
        result = prime * result + (STerminatesInnermost ? 1249 : 1259);
        this.hashCode = result;
    }

    public CpxRelTrsProblem(String shortname,
            String longname,
            ImmutableSet<Rule> R,
            ImmutableSet<Rule> S,
            RewriteStrategy rewriteStrategy,
            boolean STerminatesInnermost) {
        super(shortname, longname);
        Set<FunctionSymbol> definedSymbols = new LinkedHashSet<>();
        for (Rule r: R) {
            definedSymbols.add(r.getRootSymbol());
        }
        for (Rule r: S) {
            definedSymbols.add(r.getRootSymbol());
        }
        init(R, S, definedSymbols, rewriteStrategy, STerminatesInnermost);
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        CpxRelTrsProblem other = (CpxRelTrsProblem) obj;
        if (R == null) {
            if (other.R != null)
                return false;
        } else if (!R.equals(other.R))
            return false;
        if (S == null) {
            if (other.S != null)
                return false;
        } else if (!S.equals(other.S))
            return false;
        if (defSymbols == null) {
            if (other.defSymbols != null)
                return false;
        } else if (!defSymbols.equals(other.defSymbols))
            return false;
        if (hashCode != other.hashCode)
            return false;
        if (rewriteStrategy != other.rewriteStrategy)
            return false;
        return true;
    }



    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(getProofPurposeDescriptor().export(o));
        s.append(o.cond_linebreak());
        if (this.R.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.R, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        if (this.S.isEmpty()) {
            s.append("S is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The (relative) TRS S consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.S, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        s.append("Rewrite Strategy: " + this.rewriteStrategy);

        return s.toString();
    }

    /**
     * @return Defined symbols of R and S.
     */
    @Override
    public ImmutableSet<FunctionSymbol> getDefinedSymbols() {
        return defSymbols;
    }

    public ImmutableSet<Rule> getR() {
        return this.R;
    }

    public ImmutableSet<Rule> getS() {
        return this.S;
    }

    @Override
    public Set<Rule> getRules() {
        return this.allRules;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        return this.signature;
    }

    public RewriteStrategy getRewriteStrategy() {
        return this.rewriteStrategy;
    }

    public Set<Variable> getVariables() {
        Set<Variable> result = new LinkedHashSet<Variable>();
        for (Rule rule : this.allRules) {
            result.addAll(rule.getVariables());
        }
        return result;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public boolean isLeftLinear() {
        for (Rule r: allRules) {
            if (!r.getLeft().isLinear()) {
                return false;
            }
        }
        return true;
    }

    public boolean isBasic(TRSTerm tArg) {
        Set<FunctionSymbol> definedSymbols = getDefinedSymbols();
        if (tArg.isVariable()) {
            return false;
        }
        TRSFunctionApplication t = (TRSFunctionApplication) tArg;
        if (!definedSymbols.contains(t.getRootSymbol())) {
            return false;
        }
        return t.getNonRootFunctionSymbols().stream().allMatch(x -> !definedSymbols.contains(x));
    }

    public boolean isDefined(FunctionSymbol f) {
        return getDefinedSymbols().contains(f);
    }

    public boolean isConstructorSystem() {
        for (Rule r: allRules) {
            if (!isBasic(r.getLeft())) {
                return false;
            }
        }
        return true;
    }

    @Override
    public Set<? extends TRSTerm> getTerms() {
        return CollectionUtils.getTerms(this.allRules);
    }

    public Set<String> getUsedNames() {
        return union(
                 getSignature().stream().map(x -> x.getName()).collect(toSet()),
                 getTerms().stream().flatMap(t -> t.getVariables().stream().map(x -> x.getName())).collect(toSet())
               );
    }

    public boolean isNonDuplicating() {
        return allRules.stream().allMatch(r -> {
            Map<TRSVariable, Integer> lhsVarCount = r.getLeft().getVariableCount();
            Map<TRSVariable, Integer> rhsVarCount = r.getRight().getVariableCount();
            return r.getVariables().stream().allMatch(x -> lhsVarCount.get(x) >= rhsVarCount.getOrDefault(x, 0));
        });
    }

    public abstract boolean isDerivational();

    public abstract BasicObligation withRules(Set<Rule> renamedRules, Set<Rule> renamedRelativeRules);

    public abstract BasicObligation provedTerminationOfS();

    public boolean STerminatesInnermost() {
        return STerminatesInnermost;
    }

    @Override
    public String toExternString() {
        final StringBuilder s = new StringBuilder();
        final Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
        for (final Rule rule : this.allRules) {
            vars.addAll(rule.getVariables());
        }
        final Set<String> varNames = new LinkedHashSet<String>();
        for(final TRSVariable x : vars) {
            varNames.add(x.getName());
        }
        final Set<String> signatureNames = new LinkedHashSet<String>();
        for(final FunctionSymbol f : this.getSignature()) {
            signatureNames.add(f.getName());
        }

        final FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
        fng.lockNames(signatureNames);
        fng.lockNames(varNames);

        final Set<String> collisions = new HashSet<String>(varNames);
        collisions.retainAll(signatureNames);

        final Map<TRSVariable, TRSVariable> varMap =
            new LinkedHashMap<TRSVariable, TRSVariable>();
        for (final TRSVariable x : vars) {
            if (collisions.contains(x.toString())) {
                varMap.put(x, TRSTerm.createVariable(fng.getFreshName(
                    x.toString(), false)));
            } else {
                varMap.put(x, x);
            }
        }
        final TRSSubstitution subst =
            TRSSubstitution.create(ImmutableCreator.create(varMap));

        // output
        s.append("(GOAL COMPLEXITY)\n");
        if (isDerivational()) {
            s.append("(STARTTERM UNRESTRICTED)\n");
        }
        else {
            s.append("(STARTTERM CONSTRUCTOR-BASED)\n");
        }
        if (this.rewriteStrategy == RewriteStrategy.INNERMOST) {
            s.append("(STRATEGY INNERMOST)\n");
        }
        else if (this.rewriteStrategy == RewriteStrategy.PARALLEL_INNERMOST) {
            s.append("(STRATEGY PARALLELINNERMOST)\n");
        }
        s.append("(VAR");
        for (final TRSVariable var : varMap.values()) {
            s.append(" " + var.toString());
        }
        s.append(")\n");
        s.append("(RULES\n");
        for (Rule rule : this.R) {
            rule = rule.applySubstitution(subst);
            s.append("  " + rule.toString() + "\n");
        }
        for (Rule rule : this.S) {
            rule = rule.applySubstitution(subst);
            s.append("  " + rule.toString().replace("->", "->=") + "\n");
        }
        s.append(")\n");
        return s.toString();
    }

    @Override
    public String externName() {
        return "trs";
    }
}
