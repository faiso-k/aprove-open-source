package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import immutables.*;

public class ConstraintSet extends Constraint.ConstraintSkeleton implements Set<Constraint> {

    public final static ConstraintSet emptySet = ConstraintSet.create(new LinkedHashSet<Constraint>(0));

    ImmutableSet<Constraint> iSet = null;

    int predicateCount = 0;
    int reducesToCount = 0;
    int implicationCount = 0;

    /**
    public boolean collectUnifyProblemForEquivalenz(List<ConstraintUnifyProblem> cups, Constraint con) {

        return false;
    }

    public boolean collectUnifyProblemForImplication(Vector<Variable> yes, Vector<Variable> no, List<ConstraintUnifyProblem> cups, Constraint con, boolean multiSet) {
        if (cups.isEmpty()) return false;
        List<Constraint> acs = new LinkedList<Constraint>(); //(acs * sigma <= bcs * sigma)
        List<Constraint> bcs = new LinkedList<Constraint>(this);
        if (con.isConstraintSet()) {
            acs.addAll((ConstraintSet)con);
        } else {
            acs.add(con);
        }
        if (acs.isEmpty()) return true;
        if (bcs.isEmpty()) return false;
        int counterWidth = acs.size();
        int bound = bcs.size();
        int counter[] = new int[counterWidth];
        for (int i = 0;i<counterWidth;i++){
            counter[i]=0;
        }
        List<ConstraintUnifyProblem> ocups = new LinkedList<ConstraintUnifyProblem>(cups);
        cups.clear();
        OuterLoop:
            do {
                List<ConstraintUnifyProblem> fcups = ConstraintUnifyProblem.freshCopies(ocups);
                for (int i=0;i<counterWidth;i++){
                    Constraint a = acs.get(i);
                    Constraint b = bcs.get(counter[i]);
                    if (!preCheck(a,b)) continue OuterLoop;
                    if (!a.collectUnifyProblemForImplication(yes, no, fcups, b, false)){
                        continue OuterLoop;
                    }
                }
                cups.addAll(fcups);
            }while (countUp(counter,bound,multiSet));
        return cups.isEmpty();
    }

    private boolean countUp(int[] counter,int bound,boolean multiSet){
        for (int i=0;i<counter.length;i++) {
            do {
                counter[i]++;
            } while (!multiSet && !counterOk(counter,i));
            if  (counter[i]==bound) counter[i]=0; else return true;
        }
        return false;
    }

    private boolean counterOk(int[] counter,int j){
        for (int i=0;i<j;i++){
            if (counter[i]==counter[j]) return false;
        }
        return true;
    }

    private boolean preCheck(Constraint a,Constraint b){
        return a.isImplication() && b.isImplication() ||
        a.isPredicate() && b.isPredicate() ||
        a.isReducesTo() && b.isReducesTo();
    }

    **/

    public static ConstraintSet create(Collection<? extends Constraint> cs) {
        return new ConstraintSet().setAndFlatten(cs);
    }

    public static ConstraintSet flatCreate(Constraint... cs) {
        return ConstraintSet.create(Arrays.asList(cs));
    }

    public static ConstraintSet flatCreate(Collection<? extends Constraint> cs) {
        return ConstraintSet.create(cs);
    }

    private ConstraintSet() {
    }

    private ConstraintSet setAndFlatten(Collection<? extends Constraint> cs) {
        Set<Constraint> ncs = new LinkedHashSet<Constraint>(cs.size() * 2 + 3);
        List<Collection<? extends Constraint>> scs = new LinkedList<Collection<? extends Constraint>>();
        scs.add(cs);
        while (!scs.isEmpty()) {
            for (Constraint c : scs.remove(0)) {
                if (c instanceof ConstraintSet) {
                    scs.add((ConstraintSet) c);
                } else {
                    if (c.isImplication()) {
                        this.implicationCount++;
                    }
                    if (c.isPredicate()) {
                        this.predicateCount++;
                    }
                    if (c.isReducesTo()) {
                        this.reducesToCount++;
                    }
                    ncs.add(c);
                }
            }
        }
        this.iSet = ImmutableCreator.create(ncs);
        return this;
    }

    @Override
    public TRSVisitable visit(DPConstraintVisitor dpcv) {
        dpcv.fcaseConstraintSet(this);
        ConstraintSet cs = this;
        Set<Constraint> nCs = new LinkedHashSet<Constraint>(this.iSet.size() + 3);
        boolean change = false;
        for (Constraint c : this.iSet) {
            Constraint nC = dpcv.applyTo(c);
            change = change || nC != c;
            nCs.add(nC);
        }
        if (change) {
            cs = ConstraintSet.create(nCs);
        }
        return dpcv.caseConstraintSet(cs);
    }

    @Override
    public boolean add(Constraint o) {
        return this.iSet.add(o);
    }

    @Override
    public boolean addAll(Collection<? extends Constraint> c) {
        return this.iSet.addAll(c);
    }

    @Override
    public void clear() {
        this.iSet.clear();
    }

    @Override
    public boolean contains(Object o) {
        return this.iSet.contains(o);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return this.iSet.containsAll(c);
    }

    @Override
    public boolean equals(Object o) {
        return this.iSet.equals(o);
    }

    @Override
    public int hashCode() {
        return this.iSet.hashCode();
    }

    @Override
    public boolean isEmpty() {
        return this.iSet.isEmpty();
    }

    @Override
    public Iterator<Constraint> iterator() {
        return this.iSet.iterator();
    }

    @Override
    public boolean remove(Object o) {
        return this.iSet.remove(o);
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        return this.iSet.removeAll(c);
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        return this.iSet.retainAll(c);
    }

    @Override
    public int size() {
        return this.iSet.size();
    }

    @Override
    public Object[] toArray() {
        return this.iSet.toArray();
    }

    @Override
    public <T> T[] toArray(T[] a) {
        return this.iSet.toArray(a);
    }

    @Override
    public boolean isConstraintSet() {
        return true;
    }

    @Override
    public String toString() {
        StringBuffer sb = new StringBuffer();
        boolean notfirst = false;
        for (Constraint con : this) {
            if (notfirst) {
                sb.append("\n&");
            }
            sb.append(con.toString());
            notfirst = true;
        }
        return sb.toString();
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        boolean notfirst = false;
        for (Constraint con : this) {
            if (notfirst) {
                sb.append(o.andSign());
            } else {
                notfirst = true;
            }
            sb.append(con.export(o));
        }
        return sb.toString();
    }

    @Override
    public boolean collectMatchMap(Constraint constraint, Map<TRSVariable, TRSTerm> map) {
        return false;
    }

    @Override
    public Set<GPolyVar> getPolyVariables() {
        Set<GPolyVar> vars = new LinkedHashSet<GPolyVar>();
        for (Constraint c : this) {
            vars.addAll(c.getPolyVariables());
        }
        return ImmutableCreator.create(vars);
    }

}
