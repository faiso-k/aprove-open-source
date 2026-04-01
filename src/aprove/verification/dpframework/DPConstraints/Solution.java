package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

public class Solution {

    Map<TRSVariable, TRSTerm> map;
    Set<TRSVariable> vars;
    QuantorEntry quantorEntry;
    Stack<Set<Object>> idSets;
    Set<Object> topIdSet;
    boolean valid;

    public Solution(Set<TRSVariable> vars) {
        this.map = new LinkedHashMap<TRSVariable, TRSTerm>();
        this.vars = vars;
        this.quantorEntry = QuantorEntry.emptyQuantorEntry;
        this.valid = true;
        this.idSets = new Stack<Set<Object>>();
        this.idSets.push(null);
    }

    public TRSSubstitution getSubstitution() {
        return TRSSubstitution.create(ImmutableCreator.create(this.map));
    }

    public Set<TRSVariable> getUsedVariables() {
        return this.map.keySet();
    }

    public void reset() {
        this.map.clear();
        this.quantorEntry = QuantorEntry.emptyQuantorEntry;
        this.valid = true;
        this.idSets.clear();
        this.idSets.push(null);
    }

    public void setNotValid() {
        this.valid = false;
    }

    public boolean isValid() {
        return this.valid;
    }

    public boolean extendWith(Map<TRSVariable, TRSTerm> nmap) {
        for (Map.Entry<TRSVariable, TRSTerm> entry : nmap.entrySet()) {
            if (!this.extendWith(entry.getKey(), entry.getValue())) {
                return false;
            }
        }
        return true;
    }

    public boolean extendWith(TRSVariable v, TRSTerm t) {
        if (this.vars.contains(v)) {
            TRSTerm res = this.map.get(v);
            if (res == null) {
                this.valid = true;
                this.map.put(v, t);
            } else {
                this.valid = res.equals(t);
            }
        } else {
            this.valid = t.isVariable() && this.quantorEntry.extendWith(v, (TRSVariable) t);
        }
        return this.valid;
    }

    public boolean addQuantors(Set<TRSVariable> qa, Set<TRSVariable> qb) {
        int i = qa.size();
        if (i != qb.size()) {
            return false;
        }
        if (i == 1) {
            this.quantorEntry = new EasyRelQuantorEntry(this.quantorEntry, qa.iterator().next(), qb.iterator().next());
        } else {
            this.quantorEntry = new RelQuantorEntry(this.quantorEntry, qa, qb);
        }
        return true;
    }

    public void popQuantors() {
        this.quantorEntry = this.quantorEntry.getLast();
    }

    public void pushIdSet(Set<Object> idSet) {
        this.idSets.push(idSet);
    }

    public boolean checkIdBlocked(Object id) {
        Set<Object> cIdSet = this.idSets.peek();
        if (cIdSet != null) {
            if (cIdSet.contains(id)) {
                this.setNotValid();
                return false;
            }
            cIdSet.add(id);
        }

        return true;
    }

    public void popIdSet() {
        this.topIdSet = this.idSets.pop();
    }

    public static class EasyRelQuantorEntry extends QuantorEntry {
        QuantorEntry last;
        TRSVariable qa;
        TRSVariable qb;

        public EasyRelQuantorEntry(QuantorEntry last, TRSVariable qa, TRSVariable qb) {
            this.last = last;
            this.qa = qa;
            this.qb = qb;
        }

        @Override
        public boolean extendWith(TRSVariable b, TRSVariable a) {
            if (b.equals(this.qb)) {
                return a.equals(this.qa);
            }
            return this.last.extendWith(b, a);
        }

        @Override
        public QuantorEntry getLast() {
            return this.last;
        }

    }

    public static class RelQuantorEntry extends QuantorEntry {
        public static TRSVariable replaceMe = TRSTerm.createVariable("replaceMe");
        QuantorEntry last;
        Map<TRSVariable, TRSVariable> bamap;
        Set<TRSVariable> quantorA;

        public RelQuantorEntry(QuantorEntry last, Set<TRSVariable> quantorA, Set<TRSVariable> quantorB) {
            this.bamap = new LinkedHashMap<TRSVariable, TRSVariable>();
            this.last = last;
            for (TRSVariable b : quantorB) {
                this.bamap.put(b, RelQuantorEntry.replaceMe);
            }
            this.quantorA = new LinkedHashSet<TRSVariable>(quantorA);
        }

        @Override
        public boolean extendWith(TRSVariable b, TRSVariable a) {
            TRSVariable r = this.bamap.get(b);
            if (r == null) {
                return this.last.extendWith(b, a);
            }
            if (r == RelQuantorEntry.replaceMe) {
                if (!this.quantorA.contains(a)) {
                    return false;
                }
                this.bamap.put(b, a);
                this.quantorA.remove(a);
                return true;
            }
            return r.equals(a);
        }

        @Override
        public QuantorEntry getLast() {
            return this.last;
        }
    }

    public static class QuantorEntry {
        public static QuantorEntry emptyQuantorEntry = new QuantorEntry();

        public boolean extendWith(TRSVariable b, TRSVariable a) {
            return b.equals(a);
        }

        public QuantorEntry getLast() {
            return this;
        }
    }

    public Set<Object> getTopIdSet() {
        return this.topIdSet;
    }

}
