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

public class ItpfOr extends ItpfNAry {

    public static ItpfOr create(ImmutableSet<? extends Itpf> children) {
        return new ItpfOr(children, false, false);
    }

    protected static ItpfOr create(ImmutableSet<? extends Itpf> children, boolean isNormalized, boolean isDnf) {
        return new ItpfOr(children, isNormalized, isDnf);
    }

    public static ItpfOr create(Itpf... children) {
        return new ItpfOr(ImmutableCreator.create(new LinkedHashSet<Itpf>(Arrays.asList(children))), false, false);
    }

    protected final int hash;

    private ItpfOr(ImmutableSet<? extends Itpf> children, boolean isNormalized, boolean isDnf) {
        super(children, isNormalized, isDnf);
        this.hash = children.hashCode() + 17;
    }

    @Override
    public boolean isOr() {
        return true;
    }

    @Override
    public Itpf visit(IItpfVisitor visitor) {
        if (visitor.fcaseOr(this)) {
            Set<Itpf> newChildren = new LinkedHashSet<Itpf>();
            boolean changed = false;
            for (Itpf child : this.children) {
                Itpf newChild = visitor.applyTo(child);
                changed = changed || newChild != child;
                newChildren.add(newChild);
            }
            if (changed) {
                return visitor.caseOr(this, ImmutableCreator.create(newChildren));
            } else {
                return visitor.caseOr(this, this.children);
            }
        } else {
            return this;
        }
    }

    @Override
    public ItpfOr applySubstitutionNoCheck(TRSSubstitution sigma) {
        Set<Itpf> newChildren = new LinkedHashSet<Itpf>();
        boolean changed = false;
        for (Itpf child : this.children) {
            Itpf newChild = child.applySubstitution(sigma);
            changed = changed || newChild != child;
            newChildren.add(newChild);
        }
        if (changed) {
            return new ItpfOr(ImmutableCreator.create(newChildren), this.isNormalized, this.isDnf);
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
                res.append(o.orSign());
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
        return ((ItpfOr) obj).children.equals(this.children);
    }

    @Override
    protected Itpf doNormalization(boolean neg) {
        Set<Itpf> newChildren = new LinkedHashSet<Itpf>();
        if (neg) {
            for (Itpf child : this.children) {
                Itpf newChild = child.normalize(neg);
                if (newChild.isFalse()) {
                    return Itpf.FALSE;
                } else if (!newChild.isTrue()) {
                    newChildren.add(newChild);
                }
            }
            // check F \vee \not F
            for (Itpf child : this.children) {
                if (child.isNeg() && this.children.contains(((ItpfNeg) child).getChild())) {
                    return Itpf.TRUE;
                }
            }
            if (newChildren.isEmpty()) {
                return Itpf.FALSE;
            } else if (newChildren.size() == 1) {
                return newChildren.iterator().next();
            } else {
                return ItpfAnd.create(ImmutableCreator.create(newChildren), true, false);
            }
        } else {
            boolean changed = false;
            for (Itpf child : this.children) {
                Itpf newChild = child.normalize(neg);
                if (newChild.isTrue()) {
                    return Itpf.TRUE;
                } else if (!newChild.isFalse()) {
                    changed = changed || newChild != child;
                    newChildren.add(newChild);
                } else {
                    changed = true;
                }
            }
            // check F \wegde \not F
            for (Itpf child : this.children) {
                if (child.isNeg() && this.children.contains(((ItpfNeg) child).getChild())) {
                    return Itpf.FALSE;
                }
            }
            if (changed) {
                if (newChildren.isEmpty()) {
                    return Itpf.TRUE;
                } else if (newChildren.size() == 1) {
                    return newChildren.iterator().next();
                } else {
                    return new ItpfOr(ImmutableCreator.create(newChildren), true, false);
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
        List<List<Itpf>> all = new ArrayList<List<Itpf>>();
        for (Itpf child : this.children) {
            all.addAll(child.doDnf(neg, quantors, boundRenaming));
        }
        if (neg) {
            int allSize = all.size();
            List<List<Itpf>> res = new ArrayList<List<Itpf>>(allSize * (allSize - 1));
            for (int i = all.size()-1; i>= 0; i--) {
                for (int j = all.size()-1; j>= 0; j--) {
                    if (i == j) {
                        continue;
                    }
                    List<Itpf> comb = new ArrayList<Itpf>(all.get(i));
                    comb.addAll(all.get(j));
                    res.add(comb);
                }
            }
            return res;
        } else {
            return all;
        }
    }

    @Override
    protected void collectFreeVariables(Set<TRSVariable> variables) {
        for (Itpf child : this.children) {
            child.collectFreeVariables(variables);
        }
    }
}
