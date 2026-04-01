/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public abstract class Itpf implements Exportable, IDPExportable, Immutable {

    public static ItpfFalse FALSE = ItpfFalse.FALSE;
    public static ItpfTrue TRUE = ItpfTrue.TRUE;

    protected boolean isNormalized;
    protected boolean isDnf;
    private final Map<ItpfMark<? extends Object>, Object> marks;

    public Itpf(boolean isNormalized, boolean idDnf) {
        this.isNormalized = isNormalized;
        this.marks = new LinkedHashMap<ItpfMark<? extends Object>, Object>();
    }

    public boolean isAtom() {
        return false;
    }

    public boolean isAnd() {
        return false;
    }

    public boolean isOr() {
        return false;
    }

    public boolean isItp() {
        return false;
    }

    public boolean isNeg() {
        return false;
    }

    public boolean isUra() {
        return false;
    }

    public boolean isQuantor() {
        return false;
    }

    public boolean isAll() {
        return false;
    }

    public boolean isExists() {
        return false;
    }

    public boolean isTrue() {
        return false;
    }

    public boolean isFalse() {
        return false;
    }

    public final Itpf applySubstitution(TRSSubstitution sigma) {
        if (sigma.isEmpty()) {
            return this;
        } else {
            return this.applySubstitutionNoCheck(sigma);
        }
    }

    protected abstract Itpf applySubstitutionNoCheck(TRSSubstitution sigma);

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public boolean isNormalized() {
        return this.isNormalized;
    }

    /**
     * MAKE SURE TO SYNCHRONIZE OVER MARKS
     * @return
     */
    Map<ItpfMark<? extends Object>, Object> getMarks() {
        return this.marks;
    }

    @SuppressWarnings(value = { "unchecked" })
    public  <T extends Object> T getMark(ItpfMark<T> markType) {
        synchronized(this.marks) {
            return (T) this.marks.get(markType);
        }
    }

    public synchronized <T extends Object> boolean isMarked(ItpfMark<T> markType) {
        synchronized(this.marks) {
            return this.marks.containsKey(markType);
        }
    }

    public synchronized <T extends Object> void setMark(ItpfMark<T> markType) {
        synchronized(this.marks) {
            this.marks.put(markType, null);
        }
    }

    public synchronized <T extends Object> void setMark(ItpfMark<T> markType, T mark) {
        synchronized(this.marks) {
            this.marks.put(markType, mark);
        }
    }

    /**
     * @return formula in NNF
     */
    public final Itpf normalize() {
        if (this.isNormalized) {
            return this;
        } else {
            return this.normalize(false);
        }
    }

    protected final Itpf normalize(boolean neg) {
        Itpf result = this.doNormalization(false);
        if (result == this) {
            this.isNormalized = true;
        } else {
            this.copyLeafMarks(result);
        }
        return result;
    }

    protected abstract Itpf doNormalization(boolean neg);

    public final Itpf toDnf() {
        if (this.isDnf) {
            return this;
        } else {
            return this.toDnf(false);
        }
    }

    protected final Itpf toDnf(boolean neg) {
        LinkedList<Pair<TRSVariable, Boolean>> quantors = new LinkedList<Pair<TRSVariable, Boolean>>();
        List<List<Itpf>> result = this.doDnf(false, quantors, new FreshNameGenerator(this.getFreeVariables(), FreshNameGenerator.VARIABLES));
        Itpf quantorFree;
        if (result.isEmpty()) {
            return Itpf.FALSE;
        } else if (result.size() == 1) {
            List<Itpf> conjClause = result.iterator().next();
            if (conjClause.isEmpty()) {
                return Itpf.TRUE;
            } else if (conjClause.size() == 1) {
                Itpf res = conjClause.iterator().next();
                if (res == this) {
                    if (this.isQuantor() && quantors.size() == 1) {
                        TRSVariable var = ((ItpfQuantor) this).getVar();
                        Pair<TRSVariable, Boolean> quantification = quantors.getFirst();
                        if (quantification.x.equals(var) && quantification.y.booleanValue() == this.isAll()) {
                            this.isDnf = true;
                            this.isNormalized = true;
                            return this;
                        }
                    } else if (quantors.isEmpty()) {
                        this.isDnf = true;
                        this.isNormalized = true;
                        return this;
                    }
                }
                quantorFree = res;
            } else {
                quantorFree =  ItpfAnd.create(ImmutableCreator.create(new LinkedHashSet<Itpf>(conjClause)), true, true);
            }
        } else {
            Set<Itpf> clause = new LinkedHashSet<Itpf>();
            for (List<Itpf> conjClause : result) {
                if (conjClause.isEmpty()) {
                    return Itpf.TRUE;
                } else if (conjClause.size() == 1) {
                    clause.add(conjClause.iterator().next());
                } else {
                    clause.add(ItpfAnd.create(ImmutableCreator.create(new LinkedHashSet<Itpf>(conjClause)), true, true));
                }
            }
            quantorFree = ItpfOr.create(ImmutableCreator.create(clause), true, true);
        }
        for (Pair<TRSVariable, Boolean> quantification : quantors) {
            if (quantification.y) {
                quantorFree = ItpfAll.create(quantification.x, quantorFree, true, true);
            } else {
                quantorFree = ItpfExists.create(quantification.x, quantorFree, true, true);
            }
        }
        return quantorFree;
    }

    public Set<FunctionSymbol> getFunctionSymbols() {
        Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        this.collectFunctionSymbols(fs);
        return fs;
    }

    protected abstract void collectFunctionSymbols(Set<FunctionSymbol> fs);

    public final Set<TRSVariable> getFreeVariables() {
        Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
        this.collectFreeVariables(vars);
        return vars;
    }

    protected abstract void collectFreeVariables(Set<TRSVariable> variables);

    /**
     * @param neg
     * @param quantors Innermost quantor first!
     * @param boundRenaming
     * @return
     */
    protected abstract List<List<Itpf>> doDnf(boolean neg, LinkedList<Pair<TRSVariable, Boolean>> quantors, FreshNameGenerator boundRenaming);


    public abstract Itpf visit(IItpfVisitor visitor);

    protected void copyLeafMarks(Itpf target) {
        synchronized(this.marks) {
            synchronized(target.marks) {
                for (Map.Entry<ItpfMark<? extends Object>, Object> mark : this.marks.entrySet()) {
                    if (mark.getKey().isLeafMark()) {
                        target.marks.put(mark.getKey(), mark.getValue());
                    }
                }
            }
        }
    }

    public void copyCompatibleMarks(Itpf target, ItpfMark<? extends Object> newMark) {
        synchronized(this.marks) {
            synchronized(target.marks) {
                for (Map.Entry<ItpfMark<? extends Object>, Object> mark : this.marks.entrySet()) {
                    if (ItpfMark.isCompatible(mark.getKey(), newMark)) {
                        target.marks.put(mark.getKey(), mark.getValue());
                    }
                }
            }
        }
    }

}
