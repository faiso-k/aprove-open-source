package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.TreeAutomaton.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 */
public class TRSBoundsHelper {

    protected static class StateSubstTerm {
        private final TRSTerm t;
        private final StateSubstitution<Integer> sigma;

        public StateSubstTerm(final TRSTerm t, final StateSubstitution<Integer> sigma) {
            this.t = t;
            this.sigma = sigma;
        }

        public TRSTerm getT() {
            return this.t;
        }

        public StateSubstitution<Integer> getSigma() {
            return this.sigma;
        }

        public int size() {
            int size = this.t.getSize();
            for (final Map.Entry<TRSVariable, Integer> varCount : this.t.getVariableCount().entrySet()) {
                size -= varCount.getValue();
            }
            return size;
        }

        @Override
        public String toString() {
            return "StateSubstTerm [sigma=" + this.sigma + ", t=" + this.t + "]";
        }

    }

    /*
     * A Conflict is a tuple (t, sigma, q) with the following meaning:
     * There are no transitions in a TreeAutomaton A, so that A can be in state q after evaluating the term t with state substitution sigma.
     */
    protected static class Conflict {
        private final Rule evokingRule;
        private final TRSTerm t;
        private final StateSubstitution<Integer> sigma;
        private final int state;

        public Conflict(final TRSTerm t, final StateSubstitution<Integer> sigma, final Integer state,
                final Rule evokingRule) {
            this.t = t;

            final Map<TRSVariable, Integer> newStateSubs = new LinkedHashMap<TRSVariable, Integer>();
            final Set<TRSVariable> varsOfT = t.getVariables();
            for (final Map.Entry<TRSVariable, Integer> entry : sigma.getMap().entrySet()) {
                final TRSVariable x = entry.getKey();
                if (varsOfT.contains(x)) {
                    newStateSubs.put(x, entry.getValue());
                }
            }

            this.sigma = StateSubstitution.create(newStateSubs);
            this.state = state;
            this.evokingRule = evokingRule;
        }

        public Rule getEvokingRule() {
            return this.evokingRule;
        }

        public TRSTerm getTerm() {
            return this.t;
        }

        public StateSubstitution<Integer> getStateSubstitution() {
            return this.sigma;
        }

        public int getTargetState() {
            return this.state;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((this.evokingRule == null) ? 0 : this.evokingRule.hashCode());
            result = prime * result + ((this.sigma == null) ? 0 : this.sigma.hashCode());
            result = prime * result + this.state;
            result = prime * result + ((this.t == null) ? 0 : this.t.hashCode());
            return result;
        }

        /**
         * {@inheritDoc}
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
            final Conflict other = (Conflict) obj;
            if (this.evokingRule == null) {
                if (other.evokingRule != null) {
                    return false;
                }
            } else if (!this.evokingRule.equals(other.evokingRule)) {
                return false;
            }
            if (this.sigma == null) {
                if (other.sigma != null) {
                    return false;
                }
            } else if (!this.sigma.equals(other.sigma)) {
                return false;
            }
            if (this.state != other.state) {
                return false;
            }
            if (this.t == null) {
                if (other.t != null) {
                    return false;
                }
            } else if (!this.t.equals(other.t)) {
                return false;
            }
            return true;
        }

        @Override
        public String toString() {
            return "Conflict [sigma=" + this.sigma + ", targetState=" + this.state + ", t=" + this.t + "]";
        }
    }

    protected static class BijectiveFSToAFSMapper {
        private final Map<FunctionSymbol, AnnotatedFunctionSymbol> fSToAFS;
        private final Map<AnnotatedFunctionSymbol, FunctionSymbol> aFSToFS;

        public BijectiveFSToAFSMapper() {
            this.fSToAFS = new LinkedHashMap<FunctionSymbol, AnnotatedFunctionSymbol>();
            this.aFSToFS = new LinkedHashMap<AnnotatedFunctionSymbol, FunctionSymbol>();
        }

        public FunctionSymbol getFS(final AnnotatedFunctionSymbol aFS) {
            return this.aFSToFS.get(aFS);
        }

        public AnnotatedFunctionSymbol getAFS(final FunctionSymbol fS) {
            return this.fSToAFS.get(fS);
        }

        public void set(final FunctionSymbol fS, final AnnotatedFunctionSymbol aFS) {
            if (!this.fSToAFS.containsKey(fS)) {
                this.fSToAFS.put(fS, aFS);
                this.aFSToFS.put(aFS, fS);
            }
        }

        public ImmutableMap<FunctionSymbol, AnnotatedFunctionSymbol> getfSToAFS() {
            return ImmutableCreator.create(this.fSToAFS);
        }
    }

    /*
     * A simple Variable Generator.
     */
    protected static class VariableGenerator {

        private final Set<TRSVariable> variables;

        public VariableGenerator(final Set<TRSVariable> startingVariables) {
            final int symbolcount = startingVariables.size();
            this.variables = new HashSet<TRSVariable>(symbolcount * 5);
            this.variables.addAll(startingVariables);
        }

        public TRSVariable getFresh(final String name) {
            int i = 0;
            String currentName = name;
            TRSVariable x;
            while (true) {
                x = TRSTerm.createVariable(currentName);
                if (this.variables.add(x)) {
                    return x;
                } else {
                    currentName = name + i;
                    i++;
                }
            }
        }

    }

    /*
     * A simple function symbol generator, which is initialized with the function symbols in the original trs R and
     * creates new FunctionSymbols, which can be used as aliases for our annotated function symbols.
     */
    public static class FunctionSymbolGenerator {

        private final Set<FunctionSymbol> fs;

        public FunctionSymbolGenerator() {
            this.fs = new LinkedHashSet<FunctionSymbol>();
        }

        public FunctionSymbolGenerator(final Set<FunctionSymbol> startingFS) {
            final int symbolcount = startingFS.size();
            this.fs = new HashSet<FunctionSymbol>(symbolcount * 5);
        }

        public FunctionSymbol getFresh(final String name, final int arity) {
            int i = 0;
            String currentName = name;
            FunctionSymbol f;
            while (true) {
                f = FunctionSymbol.create(currentName, arity);
                if (this.fs.add(f)) {
                    return f;
                } else {
                    currentName = name + i;
                    i++;
                }
            }
        }

    }
}
