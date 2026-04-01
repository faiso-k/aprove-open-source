package aprove.input.Utility;

import static java.util.stream.Collectors.*;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;

public class RawPtrs {
    private final Set<TRSVariable> variables = new LinkedHashSet<TRSVariable>();
    private final Set<FunctionSymbol> functionsymbols = new LinkedHashSet<FunctionSymbol>();
    private boolean termination = false;
    private boolean ast = false;
    private boolean past = false;
    private boolean sast = false;
    private boolean basic = false;
    private boolean complexity = false;
    private RewriteStrategy strat;
    private Set<ProbabilisticRule> probabilisticRules = null;
    private Map<String, Integer> arityMap =
        new LinkedHashMap<String, Integer>();

    public Set<TRSVariable> getVariables() {
        return this.variables;
    }

    public boolean isVariable(String sym) {
        return this.variables.stream().map(x -> x.getName()).collect(toSet()).contains(sym);
    }

    public boolean isFunctionSymbol(String sym, int ar) {
        FunctionSymbol f = FunctionSymbol.create(sym, ar);
        boolean b = false;
        for(FunctionSymbol fold : this.functionsymbols) {
            b |= fold.equals(f);
        }
        return this.functionsymbols.stream().collect(toSet()).contains(f);
    }

    public Set<FunctionSymbol> getFunctionSymbols() {
        return this.functionsymbols;
    }

    public boolean isTermination() {
		return termination;
	}

	public boolean isAst() {
		return ast;
	}

	public boolean isPast() {
		return past;
	}

    public boolean isSast() {
        return sast;
    }
	
	public boolean isBasic() {
	    return basic;
	}
    
    public boolean isComplexity() {
        return complexity;
    }

    public Set<ProbabilisticRule> getProbabilisticRules() {
        return this.probabilisticRules;
    }

    public boolean isInnermost() {
        return this.strat == RewriteStrategy.INNERMOST;
    }

    public boolean isOutermost() {
        return this.strat == RewriteStrategy.OUTERMOST;
    }
    
    public void addVariable(TRSVariable x) {
        this.variables.add(x);
    }
    
    public void addFunctionSymbol(FunctionSymbol f) {
        this.functionsymbols.add(f);
    }

    public void setTermination(boolean termination) {
		this.termination = termination;
	}

	public void setAst(boolean ast) {
		this.ast = ast;
	}

	public void setPast(boolean past) {
		this.past = past;
	}

    public void setSast(boolean sast) {
        this.sast = sast;
    }
	
	public void setBasic(boolean basic) {
	    this.basic = basic;
	}
    
    public void setComplexity(boolean complexity) {
        this.complexity = complexity;
    }

    public void setFullRewriting() {
        this.strat = RewriteStrategy.FULL;
    }

    public void setInnermost() {
        this.strat = RewriteStrategy.INNERMOST;
    }

    public void setOutermost() {
        this.strat = RewriteStrategy.OUTERMOST;
    }

    public void setRewriteStrategy(RewriteStrategy strat) {
        this.strat = strat;
    }

    public void addProbabilisticRule(TRSTerm l, MultiDistribution<TRSTerm> r) {
        Set<TRSVariable> lhsvars = l.getVariables();
        Set<TRSVariable> rhsvars = new HashSet<>();
        for (Entry<Pair<TRSTerm, BigFraction>, Integer> entry : r.getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            rhsvars.addAll(term.getVariables());
        }
        if(l instanceof TRSFunctionApplication) {
            if (lhsvars.containsAll(rhsvars)) {
                if (this.probabilisticRules == null) {
                    this.probabilisticRules = new HashSet<>();
                }
                this.probabilisticRules.add(ProbabilisticRule.create((TRSFunctionApplication)l, r));
            } else {
                throw new UnhandledConstructException("probabilistic rule with free variable in the right hand side");
            }
        } else {
            throw new UnhandledConstructException("probabilistic rule with variable as left hand side");
        }
    }

    public void addArityMapEntry(String name, int arity) {
        this.arityMap.put(name, arity);
    }

    public void hasRules() {
        if (this.probabilisticRules == null) {
            this.probabilisticRules = new HashSet<>();
        }
    }
}
