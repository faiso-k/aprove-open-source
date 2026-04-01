package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

public class ConstraintComparator implements Comparator<Constraint> {

    private int getHash(Constraint o) {
        if (o.isPredicate()) {
            return 1;
        }
        if (o.isReducesTo()) {
            return 2;
        }
        if (o.isImplication()) {
            return 3;
        }
        if (o.isConstraintSet()) {
            return 4;
        }
        return 0;
    }

    private int compareSS(ConstraintSet o1, ConstraintSet o2, Map<TRSVariable, TRSVariable> map) {
        int h = o1.size() - o2.size();
        if (h == 0) {
            Iterator<Constraint> it1 = o1.iterator();
            Iterator<Constraint> it2 = o2.iterator();
            while (h == 0 && it1.hasNext()) {
                h = this.compare(it1.next(), it2.next());
            }
        }
        return h;
    }

    private int compareII(Implication o1, Implication o2, Map<TRSVariable, TRSVariable> map) {
        int l = o1.getQuantor().size();
        int h = l - o2.getQuantor().size();
        if (l != 0) {
            throw new RuntimeException("Comparator: Quantors are not empty " + o1.getQuantor());
        }
        if (h == 0) {
            h = this.compareSS(o1.getConditions(), o2.getConditions(), map);
        }
        if (h == 0) {
            h = this.compareCC(o1.getConclusion(), o2.getConclusion(), map);
        }
        return h;
    }

    private int compareAA(TermAtom o1, TermAtom o2, Map<TRSVariable, TRSVariable> map) {
        int h = this.compareTT(o1.getLeft(), o2.getLeft(), map);
        if (h == 0) {
            h = this.compareTT(o1.getRight(), o2.getRight(), map);
        }
        return h;
    }

    private int compareFF(TRSFunctionApplication o1, TRSFunctionApplication o2, Map<TRSVariable, TRSVariable> map) {
        int h = o1.getRootSymbol().hashCode() - o2.getRootSymbol().hashCode();
        for (int i = 0; h == 0 && i < o1.getArguments().size(); i++) {
            h = this.compareTT(o1.getArgument(i), o2.getArgument(i), map);
        }
        return h;
    }

    private int compareTT(TRSTerm o1, TRSTerm o2, Map<TRSVariable, TRSVariable> map) {
        if (o1.isVariable() && o2.isVariable()) {
            TRSVariable v1 = (TRSVariable) o1;
            TRSVariable v = map.get(v1);
            if (v == null) {
                v = (TRSVariable) o2;
                map.put(v1, v);
            }
            if (!v.equals(o2)) {
                return o1.hashCode() - o2.hashCode();
            }
            return 0;
        }
        if (!o1.isVariable() && !o2.isVariable()) {
            return this.compareFF((TRSFunctionApplication) o1, (TRSFunctionApplication) o2, map);
        }
        return o1.isVariable() ? -1 : 1;
    }

    private int compareCC(Constraint o1, Constraint o2, Map<TRSVariable, TRSVariable> map) {
        int l = this.getHash(o1);
        int h = l - this.getHash(o2);
        if (h == 0) {
            switch (l) {
            case 1:
            case 2:
                return this.compareAA((TermAtom) o1, (TermAtom) o2, map);
            case 3:
                return this.compareII((Implication) o1, (Implication) o2, map);
            case 4:
                return this.compareSS((ConstraintSet) o1, (ConstraintSet) o2, map);
            default:
                return o1.hashCode() - o2.hashCode();
            }
        }
        return h;
    }

    @Override
    public int compare(Constraint o1, Constraint o2) {
        // System.err.println("1: "+o1);
        // System.err.println("2: "+o2);
        int h = this.compareCC(o1, o2, new LinkedHashMap<TRSVariable, TRSVariable>());
        //System.out.println(h);
        return h;

    }

}
