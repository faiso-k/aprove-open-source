package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class ConstraintUnifyProblem implements Substitution {
    Collection<TRSVariable> vars;
    Map<TRSVariable, TRSTerm> solutionMap;

    public ConstraintUnifyProblem(Collection<TRSVariable> vars) {
        super();
        this.vars = vars;
        this.clear();
    }

    public ConstraintUnifyProblem(ConstraintUnifyProblem cup) {
        this(new LinkedHashSet<TRSVariable>(cup.vars));
        this.solutionMap.putAll(cup.solutionMap);
    }

    @Override
    public TRSTerm substitute(Variable var) {
        TRSVariable v = (TRSVariable)var;
        if (this.solutionMap == null) {
            return v;
        }
        TRSTerm t = this.solutionMap.get(v);
        return (t == null) ? v : t;
    }

    public void increaseDomain(Collection<TRSVariable> nvars) {
        this.vars.addAll(nvars);
    }

    public boolean addEquation(TRSTerm l, TRSTerm r) {
        l = l.applySubstitution(this);
        r = r.applySubstitution(this);
        if (l.equals(r)) {
            return true;
        }
        if (this.vars.contains(l)) {
            TRSVariable v = (TRSVariable) l;
            this.applySub(v, r);
            this.solutionMap.put(v, r);
            return true;
        } else if (this.vars.contains(r)) {
            TRSVariable v = (TRSVariable) r;
            this.applySub(v, l);
            this.solutionMap.put(v, l);
            return true;
        } else if (!l.isVariable() && !r.isVariable()) {
            TRSFunctionApplication fal = (TRSFunctionApplication) l;
            TRSFunctionApplication far = (TRSFunctionApplication) r;
            if (fal.getRootSymbol().equals(far.getRootSymbol())) {
                Iterator<? extends TRSTerm> itr = far.getArguments().iterator();
                for (TRSTerm la : fal.getArguments()) {
                    TRSTerm ra = itr.next();
                    if (!this.addEquation(la, ra)) {
                        return false;
                    }
                }
            }
            return true;
        }
        this.solutionMap = null;
        return false;
    }

    private void applySub(TRSVariable v, TRSTerm t) {
        TRSSubstitution subs = TRSSubstitution.create(v, t);
        for (Map.Entry<TRSVariable, TRSTerm> entry : this.solutionMap.entrySet()) {
            entry.setValue(entry.getValue().applySubstitution(subs));
        }
    }

    public TRSSubstitution getSolution() {
        if (this.solutionMap == null) {
            return null;
        }
        return TRSSubstitution.create(ImmutableCreator.create(this.solutionMap));
    }

    public boolean solutionIsRenaming() {
        for (TRSTerm m : this.solutionMap.values()) {
            if (!m.isVariable()) {
                return false;
            }
        }
        return true;
    }

    public boolean solutionIsPWDRenaming() {
        if (!this.solutionIsRenaming()) {
            return false;
        }
        Set<TRSTerm> vs = new HashSet<TRSTerm>(this.solutionMap.values());
        return vs.size() == this.solutionMap.values().size();
    }

    public void clear() {
        this.solutionMap = new LinkedHashMap<TRSVariable, TRSTerm>();
    }

    public static boolean addEquation(List<ConstraintUnifyProblem> cups, TRSTerm l, TRSTerm r) {
        Iterator<ConstraintUnifyProblem> itc = cups.listIterator();
        while (itc.hasNext()) {
            if (!itc.next().addEquation(l, r)) {
                itc.remove();
            }
        }
        return !cups.isEmpty();
    }

    public static void increaseDomain(List<ConstraintUnifyProblem> cups, Collection<TRSVariable> nvars) {
        for (ConstraintUnifyProblem cup : cups) {
            cup.increaseDomain(nvars);
        }
    }

    public static List<ConstraintUnifyProblem> freshCopies(List<ConstraintUnifyProblem> cups) {
        List<ConstraintUnifyProblem> fcups = new LinkedList<ConstraintUnifyProblem>();
        for (ConstraintUnifyProblem cup : cups) {
            fcups.add(new ConstraintUnifyProblem(cup));
        }
        return fcups;
    }
}
