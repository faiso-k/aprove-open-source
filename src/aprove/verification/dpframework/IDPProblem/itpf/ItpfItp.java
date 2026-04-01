/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class ItpfItp extends ItpfAtom {

    public static final ImmutableList<ImmutablePair<FunctionSymbol, Integer>> EMPTY_CONTEXT = ImmutableCreator.create(Collections.<ImmutablePair<FunctionSymbol, Integer>>emptyList());

    public static ItpfItp create(final TRSTerm l,
            final ItpRelation rel,
            final TRSTerm r,
            final ImmutableSet<TRSTerm> S) {
        return new ItpfItp(l, null, null, rel, r, null, null, S);
    }

    public static ItpfItp create(final TRSTerm l, final RelDependency kLeft, final ImmutableList<ImmutablePair<FunctionSymbol, Integer>> contextL,
            final ItpRelation rel,
            final TRSTerm r, final RelDependency kRight, final ImmutableList<ImmutablePair<FunctionSymbol, Integer>> contextR,
            final ImmutableSet<TRSTerm> S) {
        return new ItpfItp(l, kLeft, contextL, rel, r, kRight, contextR, S);
    }

    protected final TRSTerm l, r;
    protected final RelDependency kLeft, kRight;
    protected final ImmutableSet<TRSTerm> S;
    protected final ItpRelation relation;
    protected final int hash;
    protected final ImmutableList<ImmutablePair<FunctionSymbol, Integer>> contextL;
    protected final ImmutableList<ImmutablePair<FunctionSymbol, Integer>> contextR;

    private ItpfItp(final TRSTerm l, final RelDependency kLeft, final ImmutableList<ImmutablePair<FunctionSymbol, Integer>> contextL,
            final ItpRelation rel,
            final TRSTerm r, final RelDependency kRight, final ImmutableList<ImmutablePair<FunctionSymbol, Integer>> contextR,
            final ImmutableSet<TRSTerm> S) {
        super();
        this.l = l;
        this.kLeft = kLeft;
        this.contextL = contextL;
        this.relation = rel;
        this.r = r;
        this.kRight = kRight;
        this.contextR = contextR;
        this.S = S;
        final int prime = 31;
        int result = 1;
        result = prime * result + S.hashCode();
        result = prime * result + ((kLeft == null) ? 0 : kLeft.hashCode());
        result = prime * result + ((kRight == null) ? 0 : kRight.hashCode());
        result = prime * result + l.hashCode();
        result = prime * result + r.hashCode();
        result = prime * result + ((this.relation == null) ? 0 : this.relation.hashCode());
        this.hash = result;
    }

    @Override
    public boolean isItp() {
        return true;
    }

    public TRSTerm getL() {
        return this.l;
    }

    public TRSTerm getR() {
        return this.r;
    }

    public RelDependency getKLeft() {
        return this.kLeft;
    }

    public RelDependency getKRight() {
        return this.kRight;
    }

    public ImmutableList<ImmutablePair<FunctionSymbol, Integer>> getContextL() {
        return this.contextL;
    }

    public ImmutableList<ImmutablePair<FunctionSymbol, Integer>> getContextR() {
        return this.contextR;
    }

    public ImmutableSet<TRSTerm> getS() {
        return this.S;
    }

    public ItpRelation getRelation() {
        return this.relation;
    }

    @Override
    public int hashCode() {
        return this.hash;
    }

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
        final ItpfItp other = (ItpfItp) obj;
        return this.kLeft == other.kLeft && this.kRight == other.kRight && this.relation == other.relation
            && (this.kLeft == null || this.contextL.equals(other.contextL))
            && (this.kRight == null || this.contextR.equals(other.contextR))
            && this.l.equals(other.l) && this.r.equals(other.r) && this.S.equals(other.S);
    }

    @Override
    public ItpfItp applySubstitutionNoCheck(final TRSSubstitution sigma) {
        final TRSTerm newL = this.l.applySubstitution(sigma);
        final TRSTerm newR = this.r.applySubstitution(sigma);
        boolean changed = this.l != newL || this.r != newR;
        final Set<TRSTerm> newS = new LinkedHashSet<TRSTerm>();
        for (final TRSTerm s:this.S) {
            final TRSTerm sSigma = s.applySubstitution(sigma);
            newS.add(sSigma);
            changed = changed || s != sSigma;
        }
        return changed ? new ItpfItp(newL, this.kLeft, this.contextL, this.relation, newR, this.kRight, this.contextR, ImmutableCreator.create(newS)) : this;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(final Export_Util o) {
        return this.export(o, null, VerbosityLevel.MIDDLE);
    }

    @Override
    public String export(final Export_Util o, final IDPPredefinedMap predefinedMap, final VerbosityLevel verbosityLevel) {
        final StringBuilder sb = new StringBuilder();
        if (verbosityLevel.compareTo(VerbosityLevel.HIGH) >= 0) {
            sb.append("(aa");
        }
        sb.append(IDPExport.exportTerm(this.l, o, predefinedMap));
        if (this.kLeft != null) {
            sb.append(o.sup(this.kLeft.getK().toString()));
            sb.append(" @ ");
            boolean first = true;
            for (final ImmutablePair<FunctionSymbol, Integer> f_i : this.contextL) {
                if (!first) {
                    sb.append(":");
                } else {
                    first = false;
                }
                sb.append(f_i.x.export(o));
                sb.append("/");
                sb.append(f_i.y);
            }
        }
        sb.append(" ");
        if (!this.relation.equals(ItpRelation.TO_TRANS) ||
                ! this.r.equals(PredefinedSemanticsFactory.BOOLEAN_TERM_TRUE) ||
                verbosityLevel.compareTo(VerbosityLevel.HIGH) >= 0) {
            sb.append(this.relation.export(o));
            sb.append(" ");
            sb.append(IDPExport.exportTerm(this.r, o, predefinedMap));
        }
        if (this.kRight != null) {
            sb.append(o.sup(this.kRight.getK().toString()));
            sb.append(" @ ");
            boolean first = true;
            for (final ImmutablePair<FunctionSymbol, Integer> f_i : this.contextR) {
                if (!first) {
                    sb.append(":");
                } else {
                    first = false;
                }
                sb.append(f_i.x.export(o));
                sb.append("/");
                sb.append(f_i.y);
            }
        }
        if (verbosityLevel.compareTo(VerbosityLevel.HIGH) >= 0) {
            sb.append(", ");
            sb.append(o.set(this.S, Export_Util.NICE_SIMPLE));
            sb.append(")");
        }
        return sb.toString();
    }

    @Override
    public Itpf visit(final IItpfVisitor visitor) {
        return visitor.fcaseItp(this) ? visitor.caseItp(this) : this;
    }

    @Override
    protected Itpf doNormalization(final boolean neg) {
        if (this.relation.isReflexive() && this.l.equals(this.r)) {
            if (neg) {
                return Itpf.FALSE;
            } else {
                return Itpf.TRUE;
            }
        } else {
            if (neg) {
                return ItpfNeg.create(this, true, true);
            } else {
                return this;
            }
        }
    }

    @Override
    protected final List<List<Itpf>> doDnf(final boolean neg, final LinkedList<Pair<TRSVariable, Boolean>> quantors, final FreshNameGenerator boundRenaming) {
        final ArrayList<Itpf> inner = new ArrayList<Itpf>(1);
        final List<List<Itpf>> outer = new ArrayList<List<Itpf>>(1);
        outer.add(inner);
        if (neg) {
            inner.add(ItpfNeg.create(this, true, true));
        } else {
            inner.add(this);
        }
        return outer;
    }

    @Override
    protected void collectFreeVariables(final Set<TRSVariable> variables) {
        variables.addAll(this.l.getVariables());
        variables.addAll(this.r.getVariables());
    }

    @Override
    protected void collectFunctionSymbols(final Set<FunctionSymbol> fs) {
        this.l.collectFunctionSymbols(fs);
        this.r.collectFunctionSymbols(fs);
    }


}

