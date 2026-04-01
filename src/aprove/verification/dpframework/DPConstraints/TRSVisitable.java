package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public interface TRSVisitable extends HasTRSTerms, HasVariables {
    TRSVisitable visit(DPConstraintVisitor dpcv);

    public TRSVisitable applySubstitution(TRSSubstitution subs, boolean idpMode);

    public Set<FunctionSymbol> getFunctionSymbols();

    public Map<TRSVariable, Integer> getVariableCount();

    public TRSVisitable replaceIdById(Map<Object, Object> map);

    public abstract static class TRSVisitableSkeleton implements TRSVisitable {
        private boolean[] block;

        public void block(InfRule ir) {
            if (this.block == null) {
                this.block = new boolean[ir.getIrc().getRuleCount()];
            }
            this.block[ir.getNumber()] = true;
        }

        public boolean notBlocked(InfRule ir) {
            return this.block == null || !this.block[ir.getNumber()];
        }

        @Override
        public Set<TRSVariable> getVariables() {
            Set<TRSVariable> col = new LinkedHashSet<TRSVariable>();
            new VarCollector(col).applyTo(this);
            return col;
        }

        @Override
        public Set<FunctionSymbol> getFunctionSymbols() {
            Set<FunctionSymbol> col = new LinkedHashSet<FunctionSymbol>();
            new FunctionSymbolsCollector(col).applyTo(this);
            return col;
        }

        @Override
        public Set<? extends TRSTerm> getTerms() {
            Set<TRSTerm> col = new LinkedHashSet<TRSTerm>();
            new TermCollector(col).applyTo(this);
            return col;
        }

        @Override
        public Map<TRSVariable, Integer> getVariableCount() {
            Map<TRSVariable, Integer> map = new LinkedHashMap<TRSVariable, Integer>();
            new VarCounter(map).applyTo(this);
            return map;
        }

        @Override
        public TRSVisitable applySubstitution(TRSSubstitution subs, boolean idpMode) {
            return new SubstitutionVisitor(subs, idpMode).applyTo(this);
        }

        @Override
        public TRSVisitable replaceIdById(Map<Object, Object> map) {
            return new IdReplaceVisitor(map).applyTo(this);
        }
    }
}
