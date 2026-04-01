package aprove.verification.complexity.LowerBounds.EquationalUnification;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;


class UnificationProblem implements Iterable<UnificationProblem.Entry> {

    class Entry {

        private TRSTerm s;
        private TRSTerm t;

        private Entry(TRSTerm s, TRSTerm t) {
            super();
            this.s = s;
            this.t = t;
        }

        @Override
        public Entry clone() {
            return new Entry(this.s, this.t);
        }

        TRSTerm getS() {
            return this.s;
        }

        TRSTerm getT() {
            return this.t;
        }

        boolean isSolved() {
            if (this.s.isVariable() && !this.t.getVariables().contains(this.s)) {
                return true;
            }
            if (this.t.isVariable() && !this.s.getVariables().contains(this.t)) {
                return true;
            }
            return false;
        }

        TRSVariable getVariable() {
            assert this.isSolved();
            if (this.s.isVariable()) {
                return (TRSVariable) this.s;
            } else {
                assert this.t.isVariable();
                return (TRSVariable) this.t;
            }
        }

        TRSTerm getTerm() {
            assert this.isSolved();
            if (this.s.isVariable()) {
                return this.t;
            } else {
                assert this.t.isVariable();
                return this.s;
            }
        }

        Set<TRSVariable> getVariables() {
            Set<TRSVariable> res = new LinkedHashSet<>();
            res.addAll(this.s.getVariables());
            res.addAll(this.t.getVariables());
            return res;
        }

        void applySubstitution(TRSSubstitution sigma) {
            this.s = this.s.applySubstitution(sigma);
            this.t = this.t.applySubstitution(sigma);
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((this.s == null) ? 0 : this.s.hashCode());
            result = prime * result + ((this.t == null) ? 0 : this.t.hashCode());
            return result;
        }

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
            Entry other = (Entry) obj;
            if (this.s == null) {
                if (other.s != null) {
                    return false;
                }
            } else if (!this.s.equals(other.s)) {
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
            return this.s + " =? " + this.t;
        }

    }

    private Set<Entry> elements = new LinkedHashSet<>();

    UnificationProblem(TRSTerm s, TRSTerm t) {
        this.elements.add(new Entry(s, t));
    }

    UnificationProblem() {
        // do nothing
    }

    public UnificationProblem applySubstitution(TRSSubstitution sigma) {
        UnificationProblem res = new UnificationProblem();
        for (Entry e: elements) {
            res.add(e.s.applySubstitution(sigma), e.t.applySubstitution(sigma));
        }
        return res;
    }

    void add(TRSTerm s, TRSTerm t) {
        this.elements.add(new Entry(s, t));
    }

    @Override
    public Iterator<Entry> iterator() {
        return this.elements.iterator();
    }

    @Override
    public UnificationProblem clone() {
        UnificationProblem res = new UnificationProblem();
        for (Entry e: this.elements) {
            res.elements.add(e.clone());
        }
        return res;
    }

    boolean isAssigned(TRSVariable x) {
        boolean found = false;
        for (Entry e: this) {
            TRSTerm left = e.getS();
            TRSTerm right = e.getT();
            if (left.equals(right)) {
                continue;
            }
            boolean isAssignment = left.equals(x) && !right.getVariables().contains(x);
            isAssignment |= right.equals(x) && !left.getVariables().contains(x);
            if (isAssignment) {
                if (found) {
                    return false;
                } else {
                    found = true;
                }
            } else if (left.getVariables().contains(x) || right.getVariables().contains(x)) {
                return false;
            }
        }
        return found;
    }

    UnificationProblem union(UnificationProblem that) {
        UnificationProblem res = this.clone();
        for (Entry e: that.elements) {
            res.elements.add(e.clone());
        }
        return res;
    }

    /**
     * Check whether the given unification problem is solved, i.e. of the shape [x_1 =? t_1, ..., x_n =? t_n], where all
     * x_i are pairwise disjoint and no x_i occurs in any t_j.
     *
     * @param unificationProblem A unification problem that might be solved.
     * @return The substitution that solved the unification problem if it is solved, null otherwise.
     */
    TRSSubstitution getSolution() {
        TRSSubstitution result = TRSSubstitution.EMPTY_SUBSTITUTION;
        Set<TRSTerm> substitutedVariables = new LinkedHashSet<>();
        for (Entry e : this) {
            if (!e.isSolved()) {
                return null;
            }
            TRSTerm variable = e.getVariable();
            TRSTerm term = e.getTerm();
            // We have x_i =? t_i and x_j =? t_j, where x_i = x_j. The problem is not solved.
            if (!substitutedVariables.add(variable)) {
                return null;
            }
            result = result.compose(TRSSubstitution.create((TRSVariable) variable, term));
        }
        // Check whether one of the terms contains one of the substituted variables.
        for (TRSVariable variable : result.getDomain()) {
            for (TRSTerm term : result.getCodomain()) {
                if (term.hasSubterm(variable)) {
                    return null;
                }
            }
        }
        return result;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.elements == null) ? 0 : this.elements.hashCode());
        return result;
    }

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
        UnificationProblem other = (UnificationProblem) obj;
        if (this.elements == null) {
            if (other.elements != null) {
                return false;
            }
        } else if (!this.elements.equals(other.elements)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        return this.elements.toString();
    }

    Set<TRSVariable> getVariables() {
        Set<TRSVariable> res = new LinkedHashSet<>();
        for (Entry e: this.elements) {
            res.addAll(e.getVariables());
        }
        return res;
    }

    public UnificationProblem replaceAll(Map<TRSTerm, TRSTerm> rlMap) {
        UnificationProblem res = new UnificationProblem();
        for (Entry e: elements) {
            res.add(e.s.replaceAll(rlMap), e.t.replaceAll(rlMap));
        }
        return res;
    }

}
