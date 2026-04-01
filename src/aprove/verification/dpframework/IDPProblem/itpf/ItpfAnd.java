/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class ItpfAnd extends ItpfNAry {

    public static ItpfAnd create(ImmutableSet<? extends Itpf> children) {
        return new ItpfAnd(children, false, false);
    }

    public static ItpfAnd create(Itpf... children) {
        return new ItpfAnd(ImmutableCreator.create(new LinkedHashSet<Itpf>(Arrays.asList(children))), false, false);
    }

    protected static ItpfAnd create(ImmutableSet<? extends Itpf> children, boolean isNormalized, boolean isDnf) {
        return new ItpfAnd(children, isNormalized, isDnf);
    }

    protected final int hash;

    private ItpfAnd(ImmutableSet<? extends Itpf> children, boolean isNormalized, boolean isDnf) {
        super(children, isNormalized, isDnf);
        this.hash = children.hashCode() + 11;
    }

    @Override
    public boolean isAnd() {
        return true;
    }

    @Override
    public Itpf visit(IItpfVisitor visitor) {
        if (visitor.fcaseAnd(this)) {
            Set<Itpf> newChildren = new LinkedHashSet<Itpf>();
            boolean changed = false;
            for (Itpf child : this.children) {
                Itpf newChild = visitor.applyTo(child);
                changed = changed || newChild != child;
                newChildren.add(newChild);
            }
            if (changed) {
                return visitor.caseAnd(this, ImmutableCreator.create(newChildren));
            } else {
                return visitor.caseAnd(this, this.children);
            }
        } else {
            return this;
        }
    }

    @Override
    public ItpfAnd applySubstitutionNoCheck(TRSSubstitution sigma) {
        Set<Itpf> newChildren = new LinkedHashSet<Itpf>();
        boolean changed = false;
        for (Itpf child : this.children) {
            Itpf newChild = child.applySubstitution(sigma);
            changed = changed || newChild != child;
            newChildren.add(newChild);
        }
        if (changed) {
            return new ItpfAnd(ImmutableCreator.create(newChildren), this.isNormalized, this.isDnf);
        } else {
            return this;
        }
    }

    @Override
    public String export(Export_Util o) {
        return this.export(o, null, VerbosityLevel.MIDDLE);
    }

    @Override
    public String export(Export_Util o, IDPPredefinedMap predefinedMap, VerbosityLevel verbosityLevel) {
        StringBuilder res = new StringBuilder();
        res.append("(");
        Iterator<? extends Itpf> i = this.children.iterator();
        while(i.hasNext()) {
            res.append(i.next().export(o, predefinedMap, verbosityLevel));
            if (i.hasNext()) {
                res.append(o.andSign());
            }
        }
        res.append(")");
        return res.toString();
    }

    @Override
    public int hashCode() {
        return this.hash;
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
        return ((ItpfAnd) obj).children.equals(this.children);
    }



    @Override
    protected Itpf doNormalization(boolean neg) {
        Set<Itpf> newChildren = new LinkedHashSet<Itpf>();
        if (neg) {
            for (Itpf child : this.children) {
                Itpf newChild = child.normalize(neg);
                if (newChild.isTrue()) {
                    return Itpf.TRUE;
                } else if (!newChild.isFalse()) {
                    newChildren.add(newChild);
                }
            }
            // check F \wegde \not F
            for (Itpf child : this.children) {
                if (child.isNeg() && this.children.contains(((ItpfNeg) child).getChild())) {
                    return Itpf.FALSE;
                }
            }
            if (newChildren.isEmpty()) {
                return Itpf.FALSE;
            } else if (newChildren.size() == 1) {
                return newChildren.iterator().next();
            } else {
                return ItpfOr.create(ImmutableCreator.create(newChildren), true, false);
            }
        } else {
            boolean changed = false;
            for (Itpf child : this.children) {
                Itpf newChild = child.normalize(neg);
                if (newChild.isFalse()) {
                    return Itpf.FALSE;
                } else if (!newChild.isTrue()) {
                    changed = changed || newChild != child;
                    newChildren.add(newChild);
                } else {
                    changed = true;
                }
            }
            // check F \wegde \not F
            for (Itpf child : this.children) {
                if (child.isNeg() && this.children.contains(((ItpfNeg) child).getChild())) {
                    return Itpf.TRUE;
                }
            }
            if (changed) {
                if (newChildren.isEmpty()) {
                    return Itpf.TRUE;
                } else if (newChildren.size() == 1) {
                    return newChildren.iterator().next();
                } else {
                    return new ItpfAnd(ImmutableCreator.create(newChildren), true, false);
                }
            } else {
                return this;
            }
        }
    }

    @Override
    protected List<List<Itpf>> doDnf(boolean neg,
            LinkedList<Pair<TRSVariable, Boolean>> quantors,
            FreshNameGenerator boundRenaming) {
        if (neg) {
            List<List<Itpf>> res = new ArrayList<List<Itpf>>();
            for (Itpf child : this.children) {
                res.addAll(child.doDnf(neg, quantors, boundRenaming));
            }
            return res;
        } else {
            List<List<List<Itpf>>> all = new ArrayList<List<List<Itpf>>>();
            for (Itpf child : this.children) {
                all.add(child.doDnf(neg, quantors, boundRenaming));
            }
            int childCount = all.size();
            List<List<Itpf>> currentLiterals = new ArrayList<List<Itpf>>(childCount);
            ArrayList<Iterator<List<Itpf>>> iterators = new ArrayList<Iterator<List<Itpf>>>(childCount);
            // initialize
            for (int i = 0; i < childCount; i++) {
                Iterator<List<Itpf>> iter = all.get(i).iterator();
                if (iter.hasNext()) {
                    currentLiterals.add(iter.next());
                    iterators.add(iter);
                } else {
                    all.remove(i);
                }
            }
            List<List<Itpf>> clauses = new ArrayList<List<Itpf>>(childCount * (childCount - 1));
            while (true) {
                List<Itpf> clause = new LinkedList<Itpf>();
                for (List<Itpf> list : currentLiterals) {
                    clause.addAll(list);
                }
                clauses.add(clause);
                int nextIter = 0;
                while (nextIter < childCount && !iterators.get(nextIter).hasNext()) {
                    iterators.set(nextIter, all.get(nextIter).iterator());
                    nextIter ++;
                }
                if (nextIter >= childCount) {
                    break;
                }
                currentLiterals.set(nextIter, iterators.get(nextIter).next());
            }
            return clauses;
        }
    }
}
